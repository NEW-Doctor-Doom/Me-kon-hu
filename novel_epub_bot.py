#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Novel -> EPUB Telegram Bot (sirf standard library, ek hi file) [v11]

v11 me kya naya hai:
* EPUB me saare chapters ek hi lambe section me jud jate hain (har 100 chapters ka ek section), beech me koi
  chapter break/heading nahi -> text me badalne par 'Chapter 1 / Chapter 2 -----' jaisi lines nahi banti
* EPUB me author ka naam nahi daalta (pehle site ka naam, jaise 'Novel Phoenix', author line me aa jata tha)
* Har section ka <title> novel ka naam hota hai, 'Chapter N' nahi

v10 me kya naya hai:
* EPUB ke Contents (TOC) me ab chapter naam/number nahi aata (NO_CHAPTER_TITLES = True).
  Pehle TOC me 'Chapter 1, Chapter 2...' hote the, aur EPUB ko text me badalne wale apps/readers
  unhe heading bana ke text me daal dete the. Ab TOC me sirf novel ka naam hota hai, aur andar sirf main text.
* Chapter label wali lines (Chapter 1 / Episode 5 / Part 2 / अध्याय 3...) text se aur achhe se hat-ti hain

v9 me kya naya hai:
* Sirf ek chapter ka link (jaise .../chapter-1) bhejo to bhi Auto EPUB chalta hai:
  bot chapter page se novel ka chapter list khud dhoondh leta hai, aur 'Started at' usi chapter se shuru hota hai
* Agar site se list na mile to Auto EPUB 'Total chapters' poochta hai aur link ke pattern se list banata hai

Chalane ke liye: python novel_epub_bot.py (Pydroid3: bas Run dabao)

v8 me kya naya hai:
* Direct chapter links: ek message me kai chapter links bhejo -> bot scan nahi karega,
  seedhe un links ko chapter list maan ke range / Auto EPUB / Create karega
* Direct mode me EPUB ka naam links ke asli chapter numbers se banta hai (Chapter 21 -> [ 21-... ])
* Novel ka naam chapter URL se andaza lagta hai (folder ya file naam se)

v7 me kya naya hai:
* Range presets: No cut, 01-20, 21-100, 21-50, 51-100, 01-100, Custom
* 📝 Edit name: kisi bhi range ka EPUB naam khud likh sakte ho ('-' bhejo to default)
* 🤖 Auto EPUB: chunk size 10/20/25/35/40/50/100/custom, 'Started at' episode se shuru,
  har chunk alag EPUB, ek hi job me ek ke baad ek bante aur jaate hain
* Group Topics (forum) support: jis topic me command aayi, reply aur EPUB usi topic me jayenge
* EPUB me sirf novel ka main text: na novel naam, na chapter naam/number, na "[ N words ]", na site nav/ads

v6 me kya tha:
* EPUB ka naam/range EXACT wahi jo chuni (21-100 -> [ 21-100 ], utne hi chapters)
* Har EPUB ka alag internal ID
* Same-content (site ka block/limit page) pakad ke dobara download
* Shared keep-alive connections + fast chapter extract = tez
* DNS/scan/upload retry, streaming upload (RAM kam), badi EPUB auto-split, flood-safe edits

v5 me kya tha:
* Professional UI: banner photo, quote cards, rangeen buttons, live progress bar
* Menu navigation isi message me (Refresh / Back / Close)

v4 me kya tha:
* Ek saath MULTIPLE EPUB, per-site speed limiter, /cancel (sab) ya /cancel 3
"""
from __future__ import annotations

import hashlib
import html
import http.client
import ipaddress
import json
import os
import queue
import random
import re
import shutil
import socket
import sys
import tempfile
import threading
import time
import traceback
import unicodedata
import uuid
import zipfile
import zlib
from dataclasses import dataclass
from datetime import datetime, timezone
from functools import lru_cache
from html.parser import HTMLParser
from pathlib import Path
from urllib import error, parse, request

# ============================== CONFIG ==============================
BOT_TOKEN = ""  # Render me Environment Variable BOT_TOKEN me daalo (yahan mat likho)
ALLOWED_USERS = set()  # Render me Environment Variable ADMIN_ID me daalo (kai ID ho to comma se)
WORKERS = 48  # ek JOB ke max ek saath chapters
HOST_MAX = 128  # ek SITE par sab jobs milake max ek saath requests (alag site = alag limit)
MIN_WORKERS = 4  # block aane par bhi kam se kam itne chalenge
MAX_JOBS_PER_CHAT = 10  # ek chat me ek saath max EPUB jobs
MAX_JOBS_TOTAL = 10  # poore bot me ek saath max jobs
MAX_CHAPTERS = 3000
MAX_PAGE_BYTES = 8 * 1024 * 1024
TIMEOUT = 20  # ek request ka timeout (sec)
RETRIES = 3  # ek page ke liye network retries
CH_TRIES = 2  # ek chapter ke liye poori try (download + parse)
REPAIR_PASSES = 3  # fail chapters ko baad me dobara try karne ke round
MIN_TOC = 5
TG_LIMIT = 49 * 1024 * 1024
BANNER = ""  # /start ke upar ki photo: image ka URL ya phone par file ka path (jaise "/sdcard/banner.jpg"). Khali = bina photo
SUPPORT_URL = ""  # "https://t.me/yourname" daalo to "Contact support" button dikhega. Khali = nahi dikhega
USER_AGENTS = (
    "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 14; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36",
)
RETRY_CODES = {403, 408, 409, 425, 429, 500, 502, 503, 504, 520, 521, 522, 523, 524}
HARD_CODES = {403, 429, 503, 520, 521, 522, 523, 524}

# ---- IPv4 pehle: mobile network par broken IPv6 ki wajah se 30-120 sec hang hota tha
_orig_getaddrinfo = socket.getaddrinfo


def _ipv4_first(host, port, family=0, type=0, proto=0, flags=0):
    res = _orig_getaddrinfo(host, port, family, type, proto, flags)
    return sorted(res, key=lambda r: r[0] != socket.AF_INET)


socket.getaddrinfo = _ipv4_first

# ---- thread stack: Android par chhota default stack crash karta hai
try:
    threading.stack_size(2 * 1024 * 1024)
except (ValueError, RuntimeError):
    pass


class FetchError(Exception):
    pass


class ParseError(Exception):
    pass


class Cancelled(Exception):
    pass


# ============================== 0. SMART SPEED LIMITER (per site) ==============================
class Limiter:
    """Ek site par ek saath kitne requests chalein. Site 429/403 de to aadha, sab theek ho to tezi se wapas badhao."""

    def __init__(self, maxn, minn):
        self.max, self.min, self.limit = maxn, minn, maxn
        self.active, self.streak = 0, 0
        self.pause_until, self.last_cut = 0.0, 0.0
        self.cv = threading.Condition()

    def acquire(self):
        with self.cv:
            while self.active >= self.limit or time.monotonic() < self.pause_until:
                self.cv.wait(0.3)
            self.active += 1

    def release(self):
        with self.cv:
            self.active -= 1
            self.cv.notify_all()

    def good(self):
        with self.cv:
            self.streak += 1
            if self.streak >= 4 and self.limit < self.max:
                self.limit = min(self.max, self.limit + 4)
                self.streak = 0
                self.cv.notify_all()

    def slow_down(self, wait=0.0, hard=True):
        with self.cv:
            now = time.monotonic()
            if hard:
                if now - self.last_cut > 1.5:  # ek saath kai threads fail hon to baar-baar aadha na ho
                    self.limit = max(self.min, self.limit // 2)
                    self.last_cut = now
                self.pause_until = max(self.pause_until, now + wait)
            else:
                self.limit = max(self.min, self.limit - 1)
            self.streak = 0

    def cap(self, n):
        with self.cv:
            self.limit = max(self.min, min(self.limit, n))


_LIMITERS = {}
_LIM_LOCK = threading.Lock()


def _host_key(url):
    h = (parse.urlparse(url).hostname or "").lower()
    return h[4:] if h.startswith("www.") else h


def get_limiter(url):
    """Har site (host) ka apna limiter - alag-alag novels alag sites par ho to ek dusre ko slow nahi karte."""
    key = _host_key(url)
    with _LIM_LOCK:
        lim = _LIMITERS.get(key)
        if lim is None:
            lim = _LIMITERS[key] = Limiter(HOST_MAX, MIN_WORKERS)
        return lim


# ============================== 1. MINI DOM ==============================
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta",
        "param", "source", "track", "wbr"}
AUTOCLOSE = {"li", "p", "dt", "dd", "tr", "td", "th", "option"}
MAX_DEPTH = 200
_XML_BAD = re.compile("[\x00-\x08\x0b\x0c\x0e-\x1f\ufffe\uffff]")
_SLIM = re.compile(r"<!--.*?-->|<(script|style|noscript|svg|iframe)\b[^>]*>.*?</\1\s*>", re.I | re.S)


def slim_html(t):
    """Parse se pehle bhaari faltu cheezein hata do - parse bahut tez ho jata hai."""
    return _SLIM.sub("", t)


class Node:
    __slots__ = ("tag", "attrs", "children", "parent", "data")

    def __init__(self, tag, attrs=None, data=""):
        self.tag = tag
        self.attrs = dict(attrs or {})
        self.children = []
        self.parent = None
        self.data = data

    @property
    def is_text(self):
        return self.tag == "#text"

    def get(self, name, default=""):
        return self.attrs.get(name, default)

    def append(self, child):
        child.parent = self
        self.children.append(child)
        return child

    def remove(self):
        if self.parent is not None:
            self.parent.children = [c for c in self.parent.children if c is not self]
            self.parent = None

    def iter(self):
        stack = list(reversed(self.children))
        while stack:
            n = stack.pop()
            if n.is_text:
                continue
            yield n
            stack.extend(reversed(n.children))

    def text(self):
        out, stack = [], list(reversed(self.children))
        while stack:
            n = stack.pop()
            if n.is_text:
                out.append(n.data)
            else:
                stack.extend(reversed(n.children))
        return "".join(out)

    def select(self, selector):
        return _compile_selector(selector).run(self)

    def select_one(self, selector):
        return _compile_selector(selector).first(self)


class _Builder(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = Node("#document")
        self.stack = [self.root]

    def _open(self, tag, attrs):
        tag = tag.lower()
        if tag in AUTOCLOSE and self.stack[-1].tag == tag:
            self.stack.pop()
        node = Node(tag, {k.lower(): (v or "") for k, v in attrs})
        self.stack[-1].append(node)
        if tag not in VOID and len(self.stack) < MAX_DEPTH:
            self.stack.append(node)
            return True
        return False

    def handle_starttag(self, tag, attrs):
        self._open(tag, attrs)

    def handle_startendtag(self, tag, attrs):
        if self._open(tag, attrs):
            self.stack.pop()

    def handle_endtag(self, tag):
        tag = tag.lower()
        if tag in VOID:
            return
        for i in range(len(self.stack) - 1, 0, -1):
            if self.stack[i].tag == tag:
                del self.stack[i:]
                return

    def handle_data(self, data):
        top = self.stack[-1]
        if top.children and top.children[-1].is_text:
            top.children[-1].data += data
        else:
            top.append(Node("#text", data=data))


def parse_html(text):
    b = _Builder()
    b.feed(text)
    b.close()
    return b.root


# ---- CSS selectors: tag #id .class [attr op val], ' ' '>' ','
_TOKEN = re.compile(r"""#[\w-]+|\.[\w-]+|\[[^\]]+\]""")
_ATTR = re.compile(r"""\[\s*([\w:-]+)\s*(?:([~|^$*]?=)\s*(?:"([^"]*)"|'([^']*)'|([^\]\s]*)))?\s*\]""")


def _attr_check(name, op, val):
    def check(n):
        if name not in n.attrs:
            return False
        v = n.attrs[name]
        if op is None:
            return True
        return {"=": v == val, "~=": val in v.split(), "^=": v.startswith(val),
                "$=": v.endswith(val), "*=": val in v, "|=": v == val or v.startswith(val + "-")}.get(op, False)

    return check


def _compound(s):
    m = re.match(r"(?:\*|[A-Za-z][\w-]*)?", s)
    tag, rest, pos, checks = (m.group(0) or "").lower(), s[m.end():], 0, []
    for t in _TOKEN.finditer(rest):
        if t.start() != pos:
            raise ValueError(f"Unsupported selector: {s!r}")
        pos = t.end()
        x = t.group(0)
        if x[0] == "#":
            checks.append(lambda n, v=x[1:]: n.get("id") == v)
        elif x[0] == ".":
            checks.append(lambda n, v=x[1:]: v in n.get("class").split())
        else:
            am = _ATTR.fullmatch(x)
            if not am:
                raise ValueError(f"Bad attribute selector: {x!r}")
            val = next((g for g in am.groups()[2:] if g is not None), "")
            checks.append(_attr_check(am.group(1).lower(), am.group(2), val))
    if pos != len(rest):
        raise ValueError(f"Unsupported selector: {s!r}")
    return tag, checks


def _match_compound(n, comp):
    tag, checks = comp
    if n.is_text or n.tag == "#document":
        return False
    if tag and tag != "*" and n.tag != tag:
        return False
    return all(c(n) for c in checks)


def _match_chain(n, parts, i):
    comb, comp = parts[i]
    if not _match_compound(n, comp):
        return False
    if i == 0:
        return True
    p = n.parent
    if comb == ">":
        return p is not None and _match_chain(p, parts, i - 1)
    while p is not None:
        if _match_chain(p, parts, i - 1):
            return True
        p = p.parent
    return False


class _Selector:
    def __init__(self, groups):
        self.groups = groups

    def matches(self, n):
        return any(_match_chain(n, g, len(g) - 1) for g in self.groups)

    def run(self, root):
        return [n for n in root.iter() if self.matches(n)]

    def first(self, root):
        for n in root.iter():
            if self.matches(n):
                return n
        return None


@lru_cache(maxsize=256)
def _compile_selector(selector):
    groups = []
    for part in re.split(r",(?![^\[]*\])", selector):
        part = re.sub(r"\s>\s*", " > ", part.strip())
        if not part:
            continue
        parts, comb = [], " "
        for tok in re.split(r"\s+(?![^\[]*\])", part):
            if tok == ">":
                comb = ">"
                continue
            parts.append((comb, _compound(tok)))
            comb = " "
        groups.append(parts)
    if not groups:
        raise ValueError("Empty selector")
    return _Selector(groups)


# ---- XHTML output (bina recursion)
def esc(s):
    return _XML_BAD.sub("", html.escape(s, quote=False))


def to_xhtml(root):
    out, stack = [], [root]
    while stack:
        n = stack.pop()
        if isinstance(n, str):  # closing tag
            out.append(n)
        elif n.is_text:
            out.append(esc(n.data))
        elif n.tag in VOID:
            out.append(f"<{n.tag}/>")
        else:
            out.append(f"<{n.tag}>")
            stack.append(f"</{n.tag}>")
            stack.extend(reversed(n.children))
    return "".join(out)


# ============================== 2. CLEANER (bina recursion) ==============================
KEEP = {"p", "br", "hr", "b", "i", "u", "em", "strong", "s", "strike", "sub", "sup", "blockquote",
        "pre", "ul", "ol", "li", "div", "table", "thead", "tbody", "tr", "td", "th",
        "h1", "h2", "h3", "h4", "h5", "h6"}
DROP = {"script", "style", "iframe", "noscript", "form", "object", "embed", "link", "meta", "canvas",
        "button", "input", "select", "textarea", "svg", "audio", "video", "head", "title", "base",
        "img", "ins", "nav"}
PRUNE = {"p", "div", "li", "b", "i", "u", "em", "strong", "blockquote", "ul", "ol", "table", "tr", "td"}
JUNK = ".adsbygoogle, .ads, .code-block, .chapter-nav, .comments, #comments"


def clean(root):
    """Sirf safe tags rakho, saare attributes hatao, baaki tags unwrap."""
    stack = [root]
    while stack:
        node = stack.pop()
        out, todo = [], list(reversed(node.children))
        while todo:
            c = todo.pop()
            if c.is_text:
                out.append(c)
            elif c.tag in DROP:
                continue
            elif c.tag in KEEP:
                c.attrs = {}
                out.append(c)
                stack.append(c)
            else:  # unwrap: iske bachche isi level par process honge
                todo.extend(reversed(c.children))
        for c in out:
            c.parent = node
        node.children = out


def prune(root):
    nodes = [root] + list(root.iter())
    for node in reversed(nodes):  # bachche pehle, parent baad me
        keep = []
        for c in node.children:
            if (c.tag in PRUNE and not c.text().replace("\xa0", " ").strip()
                    and not any(d.tag == "hr" for d in c.iter())):
                continue
            keep.append(c)
        node.children = keep


# ============================== 3. HTTP (keep-alive, cookies, redirects) ==============================
@lru_cache(maxsize=512)
def _host_is_public(host, port):
    infos = None
    for attempt in range(4):  # kai links ek saath aane par DNS kabhi kabhi atak jata hai -> dobara try
        try:
            infos = socket.getaddrinfo(host, port, proto=socket.IPPROTO_TCP)
            break
        except UnicodeError:
            raise FetchError("Host resolve nahi hua") from None
        except socket.gaierror:
            if attempt == 3:
                raise FetchError("Host resolve nahi hua") from None
            time.sleep(0.5 * (attempt + 1))
    for info in infos:
        ip = ipaddress.ip_address(info[4][0].split("%")[0])
        if ip.version == 6 and ip.ipv4_mapped:
            ip = ip.ipv4_mapped
        if not ip.is_global:
            raise FetchError("Private/local address allowed nahi hai")
    return True


def check_public(url):
    try:
        p = parse.urlparse(url)
        if p.scheme not in ("http", "https") or not p.hostname:
            raise FetchError("Sirf http/https link chalega")
        _host_is_public(p.hostname, p.port or (443 if p.scheme == "https" else 80))
    except ValueError:
        raise FetchError("Link galat hai") from None


COOKIES = {}  # host -> {name: value}
_REDIRECTS = (301, 302, 303, 307, 308)
_SAFE = "/%:@!$&'()*+,;=-._~"
_IDLE = {}  # (scheme, host, port) -> khali keep-alive connections; SAB threads/jobs share karte hain (TLS handshake bachta hai)
_IDLE_LOCK = threading.Lock()


def _ua_for(host):
    return USER_AGENTS[zlib.crc32((host or "").encode()) % len(USER_AGENTS)]  # ek site = ek hi browser


def _take_conn(key, p):
    with _IDLE_LOCK:
        lst = _IDLE.get(key)
        if lst:
            return lst.pop(), True
    cls = http.client.HTTPSConnection if p.scheme == "https" else http.client.HTTPConnection
    return cls(p.hostname, p.port, timeout=TIMEOUT), False


def _give_conn(key, c):
    with _IDLE_LOCK:
        lst = _IDLE.setdefault(key, [])
        if len(lst) < 64:
            lst.append(c)
            return
    c.close()


def _get_once(url, headers):
    p = parse.urlparse(url)
    key = (p.scheme, p.hostname, p.port)
    path = parse.quote(p.path or "/", safe=_SAFE)
    if p.query:
        path += "?" + parse.quote(p.query, safe=_SAFE + "?")
    for attempt in (0, 1):
        c, reused = _take_conn(key, p)  # connection ek waqt me sirf ek thread ke paas hota hai -> response mix nahi hota
        try:
            c.request("GET", path, headers=headers)
            r = c.getresponse()
            data = r.read(MAX_PAGE_BYTES + 1)
            if r.will_close or len(data) > MAX_PAGE_BYTES or not r.isclosed():
                c.close()  # poora response nahi padha / server band kar raha hai -> reuse nahi
            else:
                _give_conn(key, c)
            return r.status, r.headers, data
        except (http.client.HTTPException, OSError):
            try:
                c.close()
            except Exception:  # noqa: BLE001
                pass
            if reused and attempt == 0:
                continue  # purana keep-alive connection toot gaya tha, naya khol ke dobara
            raise


def _get_following(url, base_headers):
    for _ in range(6):
        p = parse.urlparse(url)
        headers = dict(base_headers)
        ck = COOKIES.get(p.hostname)
        if ck:
            headers["Cookie"] = "; ".join(f"{k}={v}" for k, v in list(ck.items()))
        status, hdrs, data = _get_once(url, headers)
        for sc in hdrs.get_all("Set-Cookie") or ():
            nv = sc.split(";", 1)[0]
            if "=" in nv:
                k, v = nv.split("=", 1)
                COOKIES.setdefault(p.hostname, {})[k.strip()] = v.strip()
        loc = hdrs.get("Location")
        if status in _REDIRECTS and loc:
            url = parse.urljoin(url, loc).split("#")[0]
            check_public(url)
            continue
        return status, hdrs, data
    raise FetchError("Bahut zyada redirect")


def _inflate(data, enc):
    if enc not in ("gzip", "deflate"):
        return data
    for wbits in ((16 + zlib.MAX_WBITS,) if enc == "gzip" else (zlib.MAX_WBITS, -zlib.MAX_WBITS)):
        try:
            out = zlib.decompressobj(wbits).decompress(data, MAX_PAGE_BYTES + 1)
        except zlib.error:
            continue
        if len(out) > MAX_PAGE_BYTES:
            raise FetchError("Page bahut bada hai")
        return out
    raise FetchError("Compressed data kharab hai")


def _retry_after(h):
    try:
        return float(h.get("Retry-After", "") or 0)
    except (ValueError, AttributeError):
        return 0.0


def fetch(url, retries=RETRIES):
    check_public(url)
    p = parse.urlparse(url)
    lim = get_limiter(url)  # is site ka limiter (dusri sites ka asar nahi)
    headers = {
        "User-Agent": _ua_for(p.hostname),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Encoding": "gzip, deflate", "Accept-Language": "en-US,en;q=0.9",
        "Referer": f"{p.scheme}://{p.netloc}/"}
    last = None
    for attempt in range(retries + 1):
        try:
            lim.acquire()
            try:
                status, hdrs, data = _get_following(url, headers)
            finally:
                lim.release()
        except FetchError:
            raise
        except (http.client.HTTPException, OSError, ValueError) as e:
            last = type(e).__name__
            if isinstance(e, (socket.timeout, TimeoutError, ConnectionError)):
                lim.slow_down(hard=False)
            time.sleep(min(0.6 * (2 ** attempt), 8) + random.random() * 0.5)
            continue
        if 200 <= status < 300:
            if len(data) > MAX_PAGE_BYTES:
                raise FetchError("Page bahut bada hai")
            out = _inflate(data, hdrs.get("Content-Encoding", "").lower())
            lim.good()
            return out, hdrs.get("Content-Type", "")
        last = f"HTTP {status}"
        if status not in RETRY_CODES:
            break
        if status in HARD_CODES:
            lim.slow_down(min(max(_retry_after(hdrs), 2 * (attempt + 1)), 30))
        time.sleep(min(0.6 * (2 ** attempt), 8) + random.random() * 0.5)
    raise FetchError(f"Download fail: {last}")


def decode(data, ctype=""):
    if data.startswith(b"\xef\xbb\xbf"):
        return data[3:].decode("utf-8", "replace")
    enc = None
    m = re.search(r"charset=([\w-]+)", ctype or "", re.I)
    if m:
        enc = m.group(1)
    else:
        m = re.search(rb"""<meta[^>]+charset=["']?([\w-]+)""", data[:4096], re.I)
        if m:
            enc = m.group(1).decode("ascii", "ignore")
    for e in (enc, "utf-8"):
        if e:
            try:
                return data.decode(e)
            except (LookupError, UnicodeDecodeError):
                pass
    return data.decode("cp1252", "replace")


def get_html(url, retries=RETRIES):
    return slim_html(decode(*fetch(url, retries)))


def get_dom(url, retries=RETRIES):
    return parse_html(get_html(url, retries))


# ============================== 4. NOVEL LOGIC ==============================
def clean_text(s):
    return re.sub(r"\s+", " ", s.replace("\xa0", " ")).strip()


@dataclass
class Ref:
    title: str
    url: str
    num: int | None = None  # asli chapter number (direct links mode me URL se); TOC wali list me None


@dataclass
class Chapter:
    title: str
    body: str
    ok: bool = True


def _norm_host(url):
    h = (parse.urlparse(url).netloc or "").lower()
    return h[4:] if h.startswith("www.") else h


def _num(text, href):
    m = re.findall(r"\d+(?:\.\d+)?", text or "")
    if m:
        return float(m[0])
    m = re.findall(r"\d+(?:\.\d+)?", href or "")
    return float(m[-1]) if m else None


def find_toc(dom, url):
    """Page par sabse badi 'chapter links ki list' dhoondo (ek hi folder ke links, ek hi container me)."""
    host = _norm_host(url)
    groups = {}
    for a in dom.select("a[href]"):
        href = a.get("href").strip()
        if not href or href.startswith(("#", "javascript:", "mailto:", "tel:")):
            continue
        full = parse.urljoin(url, href).split("#")[0]
        if _norm_host(full) != host or not full.startswith("http"):
            continue
        dirpath = parse.urlparse(full).path.rsplit("/", 1)[0]
        anc = a
        for lvl in (1, 2, 3):
            anc = anc.parent
            if anc is None or anc.tag == "#document":
                break
        groups.setdefault((lvl, anc, dirpath), {}).setdefault(full, a)
    best, best_key = None, None
    for key, links in groups.items():
        n = len(links)
        if n < MIN_TOC:
            continue
        likes = sum(1 for u, a in links.items() if re.search(r"\d", a.text() + u))
        if likes < 0.5 * n:
            continue
        rank = (n, -key[0])
        if best is None or rank > best_key:
            best, best_key = links, rank
    if best is None:
        return []
    items = [(clean_text(a.text())[:150], u) for u, a in best.items()]
    nums = [_num(t, u) for t, u in items]
    known = [x for x in nums if x is not None]
    if len(known) >= 3 and known[0] > known[-1]:  # newest-first list -> ulta karo
        items.reverse()
    return [Ref(t or f"Chapter {i}", u) for i, (t, u) in enumerate(items, 1)]


_NEXT_TEXT = re.compile(r"^(next(\s+chapter|\s+ch\.?)?|[>»›→]+)\s*[>»›→]*$", re.I)
_NEXT_ID = re.compile(r"(?<![a-z])next(?![a-z])")
_FIRST_TEXT = re.compile(r"read\s(now|first|from\sstart)|start\sreading|first\schapter|^(chapter|ch\.?)\s0*1\b", re.I)


def _ok_href(h):
    h = (h or "").strip()
    return bool(h) and not h.startswith(("#", "javascript:", "mailto:"))


def find_next(dom, url):
    for n in dom.select("link[rel=next], a[rel=next]"):
        if _ok_href(n.get("href")):
            return parse.urljoin(url, n.get("href"))
    for a in dom.select("a[href]"):
        if not _ok_href(a.get("href")):
            continue
        t = clean_text(a.text())
        ident = (a.get("id") + " " + a.get("class")).lower()
        if (len(t) <= 30 and _NEXT_TEXT.match(t)) or _NEXT_ID.search(ident):
            u = parse.urljoin(url, a.get("href")).split("#")[0]
            if u != url:
                return u
    return None


def find_first_chapter(dom, url):
    for a in dom.select("a[href]"):
        if _ok_href(a.get("href")) and _FIRST_TEXT.search(clean_text(a.text())):
            return parse.urljoin(url, a.get("href")).split("#")[0]
    return None


def page_title(dom):
    h = dom.select_one("h1")
    og = dom.select_one('meta[property="og:title"]')
    t = dom.select_one("title")
    return clean_text((h.text() if h else "") or (og.get("content") if og else "")
                      or (t.text() if t else ""))[:150]


def book_info(dom, url):
    au = dom.select_one('meta[name="author"]')
    ar = dom.select_one("a[rel=author]")
    author = clean_text((au.get("content") if au else "") or (ar.text() if ar else "")) or "Unknown"
    h = dom.select_one("html")
    return {"title": plain(clean_book_title(page_title(dom))) or "Novel", "author": author[:100],
            "lang": (h.get("lang") if h and h.get("lang") else "en"), "url": url}


_TITLE_JUNK = re.compile(r"\s*(?:[-|–—]\s*)?(?:novel\sphoenix|read\s+online|all\s+chapters|chapters?\s+list)\s*$", re.I)
_TITLE_TAIL = re.compile(r"\s*(?:novel\s+)?(?:chapters?|chapter\s+list)\s*$", re.I)


def plain(s):
    """Accent hatao (Pokémon -> Pokemon) aur : ? " jaise symbols hatao -> saaf naam."""
    s = unicodedata.normalize("NFKD", s)
    s = "".join(ch for ch in s if not unicodedata.combining(ch))
    s = re.sub(r'[\\/:*?"<>|\x00-\x1f]+', " ", s)
    return re.sub(r"\s+", " ", s).strip()


_TITLE_CH = re.compile(r"(?:\s*[-|–—:]\s*|\s+)(?:chapter|chap\.?|ch\.?|episode|ep\.?)\s*\d+\b.*$", re.I)


def clean_book_title(t):
    """'Xyz - Chapter 11: Rewards - Novel Phoenix' -> 'Xyz' (chapter naam/number EPUB ke naam me nahi jaata)"""
    t = clean_text(t)
    for _ in range(3):
        t2 = _TITLE_JUNK.sub("", t)
        t2 = _TITLE_CH.sub("", t2)
        t2 = _TITLE_TAIL.sub("", t2)
        t2 = re.sub(r"\s+novel$", "", t2, flags=re.I).strip(" -|–—:")
        if t2 == t:
            break
        t = t2
    return t or "Novel"


_CH_TITLE = re.compile(r"(?:chapter|chap\.?|ch\.?|episode|ep\.?)\s*[-:#]?\s*(\d+)", re.I)
CH_URL = re.compile(r"(?:chapter|chap|ch|episode|ep)[-/]?(\d+)", re.I)


def chapter_no(ref):
    for rx, s in ((_CH_TITLE, ref.title), (CH_URL, parse.urlparse(ref.url).path)):
        m = rx.search(s or "")
        if m:
            return int(m.group(1))
    return None


def range_label(refs, url, first, full_n):
    """'[ 101-200 ]' - asli chapter numbers se, warna ?page=N se hisaab."""
    a, b = chapter_no(refs[0]), chapter_no(refs[-1])
    if a is None or b is None or b < a or (b - a + 1) > len(refs) * 3:
        q = parse.parse_qs(parse.urlparse(url).query)
        pg = q.get("page", q.get("p", ["1"]))[0]
        page = int(pg) if pg.isdigit() and int(pg) > 0 else 1
        a = (page - 1) * full_n + first
        b = a + len(refs) - 1
    return f"[ {a}-{b} ]"


CONTENT_SELECTORS = ("#chr-content", "#chapter-content", ".chapter-content", ".reading-content",
                     "#storytext", "#chapterText", ".chapter-body", "#chapter-body", ".chapter__content",
                     ".text-left", "#content", ".entry-content", ".post-content", ".prose",
                     "article", "main")
_BAD_CLS = re.compile(r"comment|sidebar|footer|menu|widget|related|share|(^|[\s_-])nav", re.I)
_BLOCK_RE = re.compile(r"just a moment|attention required|access denied|verify you are human|"
                       r"too many requests|rate limit|checking your browser|temporarily unavailable", re.I)


def smart_detect(dom):
    """Jis element me sabse zyada seedha text (paragraphs) ho wahi chapter hai."""
    best, score = None, 0
    for n in dom.iter():
        if n.tag in ("script", "style", "nav", "footer", "header", "aside", "form"):
            continue
        if _BAD_CLS.search(n.get("class") + " " + n.get("id")):
            continue
        s = 0
        for c in n.children:
            if c.is_text:
                s += len(c.data.strip())
            elif c.tag == "p":
                s += len(clean_text(c.text()))
        if s > score:
            best, score = n, s
    return best


def _index_dom(dom):
    """Ek hi pass me id/class/tag ka pehla element yaad rakho (pehle 15 baar DOM ghoomta tha)."""
    ids, cls, tags = {}, {}, {}
    for n in dom.iter():
        a = n.attrs
        v = a.get("id")
        if v and v not in ids:
            ids[v] = n
        v = a.get("class")
        if v:
            for k in v.split():
                if k not in cls:
                    cls[k] = n
        if n.tag not in tags:
            tags[n.tag] = n
    return ids, cls, tags


def extract_content(dom):
    ids, cls, tags = _index_dom(dom)
    t = tags.get("title")
    if t and _BLOCK_RE.search(t.text()) and len(clean_text(dom.text())) < 3000:
        raise ParseError("Site ne block/limit page diya")  # retry hoga
    node = None
    for sel in CONTENT_SELECTORS:
        if sel[0] == "#":
            n = ids.get(sel[1:])
        elif sel[0] == ".":
            n = cls.get(sel[1:])
        else:
            n = tags.get(sel)
        if n is not None and len(clean_text(n.text())) >= 150:
            node = n
            break
    if node is None:
        node = smart_detect(dom)
    if node is None or len(clean_text(node.text())) < 20:
        body = tags.get("body")  # last resort
        if body is not None and len(clean_text(body.text())) >= 150:
            node = body
    if node is None or len(clean_text(node.text())) < 20:
        raise ParseError("Chapter ka text nahi mila")
    return node


def _fast_pat(sel):
    n = re.escape(sel[1:])
    if sel[0] == "#":
        return re.compile(r"""<([A-Za-z][\w-]*)\b[^>]*?\bid\s*=\s*["']%s["'][^>]*>""" % n, re.I)
    if sel[0] == ".":
        return re.compile(r"""<([A-Za-z][\w-]*)\b[^>]*?\bclass\s*=\s*["'](?:[^"']*\s)?%s(?:\s[^"']*)?["'][^>]*>""" % n, re.I)
    return re.compile(r"<(%s)\b[^>]*>" % re.escape(sel), re.I)


_FAST_PATS = [_fast_pat(x) for x in CONTENT_SELECTORS]
_TAG_STRIP = re.compile(r"<[^>]+>")
_TITLE_RE = re.compile(r"<title[^>]*>(.*?)</title>", re.I | re.S)


def _balanced(text, start, tag):
    """Tag ke andar ka hissa (nested same-tag ginte hue)."""
    rx = re.compile(r"<(/?)%s\b[^>]*?(/?)>" % re.escape(tag), re.I)
    depth = 1
    for m in rx.finditer(text, start):
        if m.group(1):
            depth -= 1
            if depth == 0:
                return text[start:m.start()]
        elif not m.group(2):
            depth += 1
    return text[start:]


def fast_content(text):
    """Chapter ka container regex se dhoondh ke sirf wahi parse karo (poora page parse karne se ~5x tez).
    Na mile to None -> purana poora parse wala rasta."""
    if len(text) < 3000:
        return None
    t = _TITLE_RE.search(text)
    if t and _BLOCK_RE.search(t.group(1)):
        return None
    for pat in _FAST_PATS:
        m = pat.search(text)
        if m is None:
            continue
        frag = _balanced(text, m.end(), m.group(1))
        if len(clean_text(_TAG_STRIP.sub(" ", frag))) >= 150:
            return parse_html(frag)
    return None


def page_to_node(text):
    node = fast_content(text)
    return node if node is not None else extract_content(parse_html(text))


# ---- EPUB me sirf main novel text: novel naam, chapter naam/number, word count, nav, ads hatao
_JUNK_WORDS_RE = re.compile(r"^\[\s*[\d,.]+\s*words?\s*\]$", re.I)
_CH_LABEL_RE = re.compile(r"^(?:(?:chapter|chap\.?|episode|अध्याय|एपिसोड)\s*[-:#.]?\s*\d+(?:[\s:.\-–—|].{0,100})?"
                          r"|(?:ch\.?|ep\.?|part|भाग)\s*[-:#.]?\s*\d+)$", re.I)
_AD_RE = re.compile(r"tap to claim|free spins|bc\.?\s?game|advertisement|sponsored", re.I)
_JUNK_EXACT = {"advertisement", "ad", "<", ">", "«", "»", "‹", "›", "<<", ">>",
               "next", "previous", "prev", "menu", "chapter list", "next chapter", "previous chapter"}


def _key(s):
    return re.sub(r"[^a-z0-9]", "", s.lower())


def _is_junk(text, keys):
    t = clean_text(text)
    if not t:
        return False
    if t.lower() in _JUNK_EXACT or _JUNK_WORDS_RE.match(t):
        return True
    if len(t) > 200:  # lamba text = asli story, use mat chhedo
        return False
    if (len(t) <= 80 and _AD_RE.search(t)) or _CH_LABEL_RE.match(t):
        return True
    k = _key(t)
    # sirf wahi line hatao jo lagbhag poori novel/chapter ka naam hai (story ki line jisme naam aa jaye use nahi)
    return any(len(x) >= 4 and x in k and len(x) >= 0.7 * len(k) for x in keys)


def _strip_junk(root, keys):
    stack = [root]
    while stack:
        n = stack.pop()
        for c in list(n.children):
            if _is_junk(c.data if c.is_text else c.text(), keys):
                c.remove()
            elif not c.is_text:
                stack.append(c)


def build_body(title, node, book=""):
    wrap = Node("div")
    wrap.append(node)
    for x in wrap.select(JUNK):
        x.remove()
    clean(wrap)
    for h in wrap.select("h1, h2, h3, h4, h5, h6"):
        h.remove()  # chapter/novel naam wale headings hatao
    _strip_junk(wrap, [k for k in (_key(book or ""), _key(title or "")) if k])
    prune(wrap)
    if not clean_text(wrap.text()):
        raise ParseError("Chapter khali hai")
    return "".join(to_xhtml(c) for c in wrap.children)  # koi <h2> title nahi


def _failed(title, why):
    return Chapter(title, f"<p>[Chapter load nahi hua: {esc(str(why)[:150])}]</p>", False)


def make_chapter(title, dom, book=""):
    try:
        return Chapter(title, build_body(title, extract_content(dom), book))
    except ParseError as e:
        return _failed(title, e)


def mark_dupes(results):
    """Alag chapters ka bilkul same lamba text = site ne block/limit/home page diya. Unhe fail maano (dobara try honge)."""
    seen = {}
    for i, c in enumerate(results):
        if c is None or not c.ok:
            continue
        t = clean_text(_TAG_STRIP.sub(" ", c.body))
        if len(t) >= 200:
            seen.setdefault(hashlib.sha1(t.encode("utf-8", "ignore")).digest(), []).append(i)
    n = 0
    for idxs in seen.values():
        if len(idxs) > 1:
            for i in idxs:
                results[i] = _failed(results[i].title, "site ne same content diya")
                n += 1
    return n


def fetch_chapter(ref, tries=CH_TRIES, cancel=None, book=""):
    """Download + parse, fail ho to thoda ruk ke dobara (har baar naya page)."""
    why = None
    for i in range(tries):
        if cancel is not None and cancel.is_set():
            break
        try:
            return Chapter(ref.title, build_body(ref.title, page_to_node(get_html(ref.url)), book))
        except FetchError as e:
            why = e
            if "HTTP 404" in str(e) or "HTTP 410" in str(e):
                break  # chapter hai hi nahi, retry bekaar
        except Exception as e:  # noqa: BLE001 (ek chapter poora kaam na roke)
            why = e
        time.sleep(min(1.0 * (i + 1), 5) + random.random())
    return _failed(ref.title, why or "cancel")


# ============================== 5. EPUB ==============================
def _page(title, body, lang):
    lg = html.escape(lang, quote=True)
    return ('<?xml version="1.0" encoding="utf-8"?>\n<!DOCTYPE html>\n'
            f'<html xmlns="http://www.w3.org/1999/xhtml" xmlns:epub="http://www.idpf.org/2007/ops" lang="{lg}" xml:lang="{lg}">\n'
            f'<head><meta charset="utf-8"/><title>{esc(title)}</title>'
            '<link rel="stylesheet" type="text/css" href="styles.css"/></head>\n'
            f'<body>\n{body}\n</body></html>')


MERGE_SECTIONS = True  # True = chapters ek hi section me jude (har MERGE_CHUNK chapters ke baad naya section)
MERGE_CHUNK = 100
NO_AUTHOR = True  # True = EPUB me author ka naam nahi
NO_CHAPTER_TITLES = True  # True = EPUB ke Contents me chapter naam/number nahi; False = purana (har chapter ka naam)
CSS = "body{margin:5%;line-height:1.5}\nh1,h2{text-align:center}\np{margin:.6em 0}\n"


def pack_epub(info, chapters, out):
    lang = info["lang"]
    sig = hashlib.sha1("|".join(f"{c.title}:{len(c.body)}" for c in chapters).encode("utf-8", "ignore")).hexdigest()
    # har range/content ka alag ID, warna reader (Moon+ etc.) alag EPUB ko ek hi book samajh ke purana content dikhata hai
    ident = "urn:uuid:" + str(uuid.uuid5(uuid.NAMESPACE_URL, f'{info["url"]}|{info["title"]}|{sig}'))
    mod = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    step = MERGE_CHUNK if MERGE_SECTIONS else 1
    bodies = ["\n".join(c.body for c in chapters[i:i + step]) for i in range(0, len(chapters), step)]
    names = [f"Section{i:04d}.xhtml" for i in range(1, len(bodies) + 1)]
    manifest = ['<item id="nav" href="nav.xhtml" media-type="application/xhtml+xml" properties="nav"/>',
                '<item id="ncx" href="toc.ncx" media-type="application/x-dtbncx+xml"/>',
                '<item id="css" href="styles.css" media-type="text/css"/>']
    manifest += [f'<item id="s{i}" href="{n}" media-type="application/xhtml+xml"/>' for i, n in enumerate(names, 1)]
    spine = "".join(f'<itemref idref="s{i}"/>' for i in range(1, len(names) + 1))
    opf = ('<?xml version="1.0" encoding="utf-8"?>\n<package xmlns="http://www.idpf.org/2007/opf" '
           'unique-identifier="bookid" version="3.0">\n<metadata xmlns:dc="http://purl.org/dc/elements/1.1/">\n'
           f'<dc:identifier id="bookid">{ident}</dc:identifier><dc:title>{esc(info["title"])}</dc:title>'
           + ("" if NO_AUTHOR else f'<dc:creator>{esc(info["author"])}</dc:creator>') +
           f'<dc:language>{esc(lang)}</dc:language>'
           f'<meta property="dcterms:modified">{mod}</meta></metadata>\n<manifest>\n' + "\n".join(manifest) +
           f'\n</manifest>\n<spine toc="ncx">{spine}</spine>\n</package>')
    if NO_CHAPTER_TITLES:  # TOC me sirf ek entry (novel ka naam), chapter naam/number nahi
        toc_items = [(names[0], info["title"])]
    else:
        toc_items = [(n, chapters[i * step].title) for i, n in enumerate(names)]
    nav_li = "".join(f'<li><a href="{n}">{esc(t)}</a></li>' for n, t in toc_items)
    nav = _page("Contents", f'<nav epub:type="toc" id="toc"><h1>Contents</h1><ol>{nav_li}</ol></nav>', lang)
    points = "".join(f'<navPoint id="n{i}" playOrder="{i}"><navLabel><text>{esc(t)}</text></navLabel>'
                     f'<content src="{n}"/></navPoint>' for i, (n, t) in enumerate(toc_items, 1))
    ncx = ('<?xml version="1.0" encoding="utf-8"?>\n<ncx xmlns="http://www.daisy.org/z3986/2005/ncx/" version="2005-1">'
           f'<head><meta name="dtb:uid" content="{ident}"/><meta name="dtb:depth" content="1"/></head>'
           f'<docTitle><text>{esc(info["title"])}</text></docTitle><navMap>{points}</navMap></ncx>')
    container = ('<?xml version="1.0"?>\n<container version="1.0" xmlns="urn:oasis:names:tc:opendocument:xmlns:container">'
                 '<rootfiles><rootfile full-path="OEBPS/content.opf" media-type="application/oebps-package+xml"/>'
                 '</rootfiles></container>')

    def b(s):
        return s.encode("utf-8", "replace")

    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED, compresslevel=4) as z:  # level 4 = tez + chhota
        z.writestr(zipfile.ZipInfo("mimetype"), "application/epub+zip", compress_type=zipfile.ZIP_STORED)
        z.writestr("META-INF/container.xml", b(container))
        for name, text in (("content.opf", opf), ("nav.xhtml", nav), ("toc.ncx", ncx), ("styles.css", CSS)):
            z.writestr(f"OEBPS/{name}", b(text))
        for n, body in zip(names, bodies):
            z.writestr(f"OEBPS/{n}", b(_page(info["title"], body, lang)))  # andar koi chapter heading nahi
    return out


_PUNCT = str.maketrans({"’": "'", "‘": "'", "“": '"', "”": '"', "–": "-", "—": "-",
                        "…": "...", "\u00a0": " "})


def ascii_clean(s):
    """'Pokémon: The X' -> 'Pokemon The X' (accent hatao, : jaise bure chars hatao, space/[ ]/- rakho)."""
    s = unicodedata.normalize("NFKD", s.translate(_PUNCT))
    s = "".join(ch for ch in s if not unicodedata.combining(ch)).encode("ascii", "ignore").decode()
    s = re.sub(r'[\/\\:*?"<>|\x00-\x1f]+', "", s)
    return re.sub(r"\s+", " ", s).strip(" .")


def safe_filename(s, limit=80):
    out = ascii_clean(s)
    if not out:  # Hindi/Unicode naam ho to ASCII khali ho jata hai -> sirf illegal chars hatao
        out = re.sub(r'[\\/:*?"<>|\x00-\x1f]+', "", s).strip(" .")
    return (out or "novel")[:limit].strip(" .")


# Telegram server upload par file name ke ASCII space / [ ] - ( ) , . ' ! sab ko '_' bana deta hai
# (letters/digits aur non-ASCII chars rehte hain). Isliye inhe dikhne me same Unicode chars se badal dete hain.
FANCY_FILENAME = True
_FANCY = str.maketrans({" ": "\u2002", "[": "\uff3b", "]": "\uff3d", "-": "\u2013", "(": "\uff08",
                        ")": "\uff09", ",": "\uff0c", "'": "\u2019", "!": "\uff01", "&": "\uff06",
                        ".": "\u2024", "#": "\uff03", "+": "\uff0b", "=": "\uff1d", ";": "\uff1b",
                        "@": "\uff20", "~": "\uff5e", "$": "\uff04", "%": "\uff05", "^": "\uff3e"})


def tg_filename(name):
    """Extension (.epub) isme nahi aata - wo baad me joda jata hai."""
    return name.translate(_FANCY) if FANCY_FILENAME else name


# ============================== 6. TELEGRAM ==============================
class TelegramError(Exception):
    def __init__(self, msg, retry_after=0):
        super().__init__(msg)
        self.retry_after = retry_after


def _multipart(fields, files):
    b = uuid.uuid4().hex
    out = []
    for k, v in fields.items():
        out.append(f'--{b}\r\nContent-Disposition: form-data; name="{k}"\r\n\r\n{v}\r\n'.encode())
    for k, (fname, data, mime) in files.items():
        fname = re.sub(r'[\r\n"]', "_", fname)
        out.append(f'--{b}\r\nContent-Disposition: form-data; name="{k}"; filename="{fname}"\r\n'
                   f"Content-Type: {mime}\r\n\r\n".encode() + data + b"\r\n")
    out.append(f"--{b}--\r\n".encode())
    return b"".join(out), f"multipart/form-data; boundary={b}"


class TelegramAPI:
    def __init__(self, token):
        self.token = token
        self.base = "https://api.telegram.org"

    def call(self, method, params=None, files=None, timeout=20):
        if files:
            body, ctype = _multipart({k: str(v) for k, v in (params or {}).items()}, files)
        else:
            body, ctype = json.dumps(params or {}).encode(), "application/json"
        req = request.Request(f"{self.base}/bot{self.token}/{method}", data=body, headers={"Content-Type": ctype})
        try:
            with request.urlopen(req, timeout=timeout) as r:
                data = json.loads(r.read())
        except error.HTTPError as e:
            try:
                data = json.loads(e.read())
            except ValueError:
                raise TelegramError(f"{method}: HTTP {e.code}") from None
        except (error.URLError, OSError, ValueError, http.client.HTTPException) as e:
            raise TelegramError(f"{method}: network error ({type(e).__name__})") from None
        if not data.get("ok"):
            ra = (data.get("parameters") or {}).get("retry_after") or 0
            raise TelegramError(f"{method}: {data.get('description', 'error')}", ra)
        return data["result"]

    def upload(self, method, params, field, path, fname, mime, timeout=600):
        """File disk se chunk-chunk bhejo (poori file RAM me nahi aati)."""
        b = uuid.uuid4().hex
        head = "".join(f'--{b}\r\nContent-Disposition: form-data; name="{k}"\r\n\r\n{v}\r\n'
                       for k, v in params.items()).encode()
        fname = re.sub(r'[\r\n"]', "_", fname)
        head += (f'--{b}\r\nContent-Disposition: form-data; name="{field}"; filename="{fname}"\r\n'
                 f"Content-Type: {mime}\r\n\r\n").encode()
        tail = f"\r\n--{b}--\r\n".encode()
        total = len(head) + os.path.getsize(path) + len(tail)

        def body():
            yield head
            with open(path, "rb") as f:
                while True:
                    chunk = f.read(262144)
                    if not chunk:
                        break
                    yield chunk
            yield tail

        req = request.Request(f"{self.base}/bot{self.token}/{method}", data=body(),
                              headers={"Content-Type": f"multipart/form-data; boundary={b}",
                                       "Content-Length": str(total)})
        try:
            with request.urlopen(req, timeout=timeout) as r:
                data = json.loads(r.read())
        except error.HTTPError as e:
            try:
                data = json.loads(e.read())
            except ValueError:
                raise TelegramError(f"{method}: HTTP {e.code}") from None
        except (error.URLError, OSError, ValueError, http.client.HTTPException) as e:
            raise TelegramError(f"{method}: network error ({type(e).__name__})") from None
        if not data.get("ok"):
            ra = (data.get("parameters") or {}).get("retry_after") or 0
            raise TelegramError(f"{method}: {data.get('description', 'error')}", ra)
        return data["result"]


# ============================== 7. UI (banner + quote cards + coloured buttons) ==============================
URL_RE = re.compile(r'https?://[^\s<>"\']+')
RANGE_RE = re.compile(r"(?<!\d)(\d+)\s*[-–—]\s*(\d*)(?!\d)")
SESSION_TTL = 1800  # link bhejne ke baad range chunne ke liye 30 min
STATS_FILE = Path(__file__).resolve().with_name("epub_stats.json") if "__file__" in globals() else Path("epub_stats.json")
_stats_lock = threading.Lock()


def hx(s):
    return html.escape(str(s), quote=False)


def cut(s, n):
    s = str(s)
    return s if len(s) <= n else s[:n - 1] + "…"


def _fmt(sec):
    sec = int(max(sec, 0))
    return f"{sec // 60}:{sec % 60:02d}"


def bar(done, total, width=12):
    frac = 0.0 if total <= 0 else min(done / total, 1.0)
    f = int(round(frac * width))
    return "▰" * f + "▱" * (width - f), int(frac * 100)


def stats_get():
    try:
        return json.loads(STATS_FILE.read_text("utf-8"))
    except Exception:  # noqa: BLE001
        return {}


def stats_add(uid):
    with _stats_lock:
        d = stats_get()
        d[str(uid)] = d.get(str(uid), 0) + 1
        try:
            STATS_FILE.write_text(json.dumps(d), "utf-8")
        except OSError:
            pass


PREFS_FILE = STATS_FILE.with_name("epub_prefs.json")
# (key, first, last) - yahan badal sakte ho. Keys purani saved defaults ke liye same rakhe hain.
PRESETS = (("r1", 1, 20), ("r2", 21, 100), ("r3", 1, 100), ("r4", 21, 50), ("r5", 51, 100))
PRESET_MAP = {k: (a, b) for k, a, b in PRESETS}
GRID = ("r1", "r2", "r4", "r5", "r3")  # buttons ka order (grid me dikhane ke liye)
AUTO_SIZES = (10, 20, 25, 35, 40, 50, 100)


def span_label(a, b):
    return f"{a:02d}-{b}" if b else f"{a:02d}-end"


def prefs_get(uid):
    try:
        return json.loads(PREFS_FILE.read_text("utf-8")).get(str(uid)) or {}
    except Exception:  # noqa: BLE001
        return {}


def prefs_save(uid, pref):
    with _stats_lock:
        try:
            d = json.loads(PREFS_FILE.read_text("utf-8"))
        except Exception:  # noqa: BLE001
            d = {}
        d[str(uid)] = pref
        try:
            PREFS_FILE.write_text(json.dumps(d), "utf-8")
        except OSError:
            pass


SEP = "─" * 18


def card(title, sub=None, rows=(), quote=(), foot=None):
    """Header (bold + italic) -> line -> text -> quote box -> bold footer. Sab text yahin escape hota hai."""
    out = [f"<b>{hx(title)}</b>"]
    if sub:
        out.append(f"<i>{hx(sub)}</i>")
    out.append(SEP)
    if rows:
        out.append("\n".join(hx(r) for r in rows))
    if quote:
        out.append("<blockquote>" + "\n".join(hx(q) for q in quote) + "</blockquote>")
    if foot:
        out.append(f"<b>{hx(foot)}</b>")
    return "\n".join(out)


def btn(text, data, style=None):
    """style: 'primary' (neela), 'success' (hara), 'danger' (laal). Purane Telegram app me normal dikhta hai."""
    b = {"text": text, "callback_data": data}
    if style:
        b["style"] = style
    return b


def kb(*rows):
    return {"inline_keyboard": [list(r) for r in rows if r]}


def menu_kb():
    rows = [[btn("📖 How to use", "m:help", "primary")],
            [btn("📋 My Jobs", "m:jobs", "success"), btn("📊 Status", "m:status", "primary")],
            [btn("🛑 Cancel all", "ca", "danger")]]
    if SUPPORT_URL:
        rows[-1].append({"text": "💬 Contact support", "url": SUPPORT_URL})
    return kb(*rows)


def nav_kb(*top):
    """Har screen ke neeche: Back (menu par) aur Close (message hata do)."""
    return kb(*top, [btn("⬅ Back", "m:menu"), btn("✖ Close", "m:close", "danger")])


HELP_CARD = card("📖 How to use", "Novel → EPUB in 3 steps", [
    "1️⃣ Novel ka link bhejo",
    "2️⃣ Total chapters dikhenge, range chuno",
    "3️⃣ EPUB ready hote hi mil jayegi",
], [
    "⚡ Shortcut · link ke baad range likho",
    "https://site.com/novel/x 5-50",
    "🔗 Chapter links · kai chapter links ek message me bhejo (ek ke neeche ek)",
    "🤖 Auto EPUB · 10/20/25… chapters ke alag EPUB",
    "📝 Edit name · EPUB ka naam khud likho",
    "📚 Kai EPUB · kai links ek saath bhejo",
], "/jobs · /cancel · /resetdefault")


def guess_title(url):
    """Chapter link se novel ka naam andaza lagao: pehle folder naam, nahi to file naam ka pehla hissa."""
    parts = [p for p in parse.urlparse(url).path.split("/") if p]
    for p in reversed(parts[:-1]):
        if not re.search(r"chapter|chap|episode|^ch-|^\d+$", p, re.I):
            name = parse.unquote(p).replace("-", " ").replace("_", " ").strip()
            if name:
                return name.title()[:120]
    last = re.sub(r"\.\w+$", "", parts[-1]) if parts else ""
    head = re.split(r"(?:^|[-_])(?:chapter|chap|episode|ch|ep)[-_]?\d", last, maxsplit=1, flags=re.I)[0]
    name = parse.unquote(head).replace("-", " ").replace("_", " ").strip()
    if name:
        return name.title()[:120]
    return _host_key(url)


def parent_urls(url):
    """https://s.com/novel/x/chapter-1 -> [https://s.com/novel/x, https://s.com/novel]"""
    p = parse.urlparse(url)
    segs = [s for s in p.path.split("/") if s]
    return [parse.urlunparse((p.scheme, p.netloc, "/" + "/".join(segs[:n]), "", "", ""))
            for n in range(len(segs) - 1, 0, -1)]


def resolve_toc(dom, url):
    """Chapter page se novel ka chapter list dhoondo: pehle page ke parent-links, phir URL ka parent folder.
    Return: (refs, toc_dom, toc_url) ya ([], None, None)."""
    host = _norm_host(url)
    base = url.split("?")[0].rstrip("/")
    cands = []
    for a in dom.select("a[href]"):
        h = a.get("href").strip()
        if not _ok_href(h):
            continue
        full = parse.urljoin(url, h).split("#")[0].split("?")[0]
        segs = [s for s in parse.urlparse(full).path.split("/") if s]
        if (_norm_host(full) == host and len(segs) >= 2 and base.startswith(full.rstrip("/") + "/")
                and full not in cands):
            cands.append(full)
    cands.sort(key=len, reverse=True)  # sabse paas wala parent pehle
    for u in parent_urls(url)[:2]:
        if u not in cands:
            cands.append(u)
    for u in cands[:4]:
        try:
            d = get_dom(u, 3)
        except FetchError:
            continue
        refs = find_toc(d, u)
        if refs:
            return refs, d, u
    return [], None, None


_NUM_IN_URL = re.compile(r"(chapter|chap|ch|episode|ep)([-_/]?)(\d+)", re.I)


def synth_refs(url, total):
    """Chapter list na mile to link ke pattern se banao: .../chapter-1 -> chapter-1 ... chapter-total."""
    p = parse.urlparse(url)
    ms = list(_NUM_IN_URL.finditer(p.path))
    if not ms or total < 1:
        return []
    m = ms[-1]
    refs = []
    for n in range(1, total + 1):
        path = p.path[:m.start(3)] + str(n) + p.path[m.end(3):]
        refs.append(Ref(f"Chapter {n}", parse.urlunparse(p._replace(path=path, query="", fragment="")), n))
    return refs


class Session:
    """Link scan ho gaya, user ke range chunne ka intezaar."""
    __slots__ = ("sid", "chat", "url", "info", "refs", "dom", "mid", "t", "uid", "sel", "custom",
                 "thread", "names", "auto", "start_at")

    def __init__(self, sid, chat, url):
        self.sid, self.chat, self.url = sid, chat, url
        self.info, self.refs, self.dom, self.mid = None, [], None, None
        self.t = time.monotonic()
        self.uid, self.sel, self.custom = 0, "all", None
        self.thread = None  # Telegram forum topic ID (group topics ke liye)
        self.names = {}  # "first-last" -> EPUB ka naam ; "auto" -> auto EPUBs ka base naam
        self.auto = 0  # Auto EPUB ka chunk size (0 = abhi nahi chuna)
        self.start_at = 1  # Auto EPUB kis episode se shuru ho


class Job:
    __slots__ = ("jid", "chat", "uid", "url", "first", "last", "cancel", "mid", "name", "title", "done",
                 "total", "thread", "tag")

    def __init__(self, jid, chat, uid, url, first, last, mid, title, thread=None):
        self.jid, self.chat, self.uid, self.url, self.first, self.last = jid, chat, uid, url, first, last
        self.cancel = threading.Event()
        self.mid, self.title = mid, title
        self.name = _host_key(url)
        self.done, self.total = 0, 0
        self.thread = thread  # jis topic me command aayi thi, wahi par EPUB jayegi
        self.tag = ""  # Auto EPUB me "[2/5] " jaisa prefix progress me

    def rng(self):
        return f"{self.first}–{self.last or 'end'}"


def job_kb(job):
    return kb([btn("✖ Cancel job", f"j:{job.jid}", "danger")])


def parse_range(text, total):
    """'1-20', '55-60', '5-' ya sirf '7' -> (first, last) ya (None, error)."""
    m = RANGE_RE.search(text)
    if m:
        first, last = int(m.group(1)), int(m.group(2) or 0)
    else:
        m = re.fullmatch(r"\s*(\d+)\s*", text)
        if not m:
            return None, "Aise likho: 1-20 ya 55-60"
        first = last = int(m.group(1))
    if first < 1:
        return None, "Chapter number 1 se shuru hota hai"
    if last and last < first:
        return None, f"Range galat hai ({first}-{last})"
    if total:
        if first > total:
            return None, f"Novel me sirf {total} chapters hain"
        last = min(last or total, total)
    return (first, last), None


def _norm_url(u):
    p = parse.urlparse(u)
    host = p.netloc.lower()
    host = host[4:] if host.startswith("www.") else host
    return (host + p.path.rstrip("/")).lower()


def find_link_pos(refs, url):
    """Link wale chapter ki position TOC me (1 = pehla chapter). Nahi mila to None."""
    if not refs:
        return None
    want = _norm_url(url)
    for i, r in enumerate(refs, 1):
        if _norm_url(r.url) == want:
            return i
    n = chapter_no(Ref("", url))  # URL ke number se fallback (jaise chapter-21)
    if n is not None:
        for i, r in enumerate(refs, 1):
            if chapter_no(r) == n:
                return i
    return None


def shift_range(rng, start, total):
    """Saved default range ko link wale chapter se shuru karo; utni hi length rahe."""
    first, last = rng
    length = (last - first + 1) if last else total
    return start, min(start + length - 1, total)


_UPLOAD_SEM = threading.Semaphore(3)


class Bot:
    def __init__(self, api, allowed=None):
        self.api = api
        self.allowed = set(allowed or ())
        self.jobs = {}  # jid -> Job
        self.sessions = {}  # sid -> Session
        self.awaiting = {}  # chat -> (sid, kind, key)  kind: range / name / start / asize
        self.next_id = 1
        self.next_sid = 1
        self.lock = threading.Lock()
        self._last_edit = {}  # (chat, message_id) -> time
        self._flood_until = 0.0  # Telegram ne "ruko" kaha to tab tak edits band
        self._banner_id = None  # Telegram file_id (pehli baar bhejne ke baad cache)
        self._photos = set()  # (chat, message_id) jo photo+caption wale hain
        self._tl = threading.local()  # us message/callback ka topic ID (main thread me set hota hai)

    # ---- chhote helpers
    def say(self, chat, text, markup=None, thread=None):
        if thread is None:
            thread = getattr(self._tl, "thread", None)
        p = {"chat_id": chat, "text": text[:4000], "parse_mode": "HTML", "disable_web_page_preview": True}
        if thread:
            p["message_thread_id"] = thread  # ye forum topic ke andar jayega
        if markup:
            p["reply_markup"] = markup
        for attempt in range(3):
            try:
                return self.api.call("sendMessage", p, timeout=15)["message_id"]
            except TelegramError as e:
                print("sendMessage failed:", e, file=sys.stderr)
                if thread and "thread" in str(e).lower():
                    # topic delete ho gaya ho to General me bhej do
                    p.pop("message_thread_id", None)
                    thread = None
                    continue
                if e.retry_after and attempt < 2:
                    time.sleep(min(e.retry_after, 10) + 0.5)
                    continue
                return None
            except Exception:  # noqa: BLE001
                return None
        return None

    def edit(self, chat, mid, text, markup=None, throttle=True):
        if mid is None:
            return
        key = (chat, mid)
        now = time.monotonic()
        if throttle and (now < self._flood_until or now - self._last_edit.get(key, 0) < max(3.0, float(len(self.jobs)))):  # jobs zyada = edits dheere (flood se bachne ko)
            return
        self._last_edit[key] = now
        if len(self._last_edit) > 2000:  # memory leak roko
            self._last_edit.clear()
        p = {"chat_id": chat, "message_id": mid, "parse_mode": "HTML"}
        if markup is not None:
            p["reply_markup"] = markup  # markup na do to buttons hat jate hain
        try:
            if key in self._photos:
                self.api.call("editMessageCaption", dict(p, caption=text[:1000]), timeout=15)
            else:
                self.api.call("editMessageText", dict(p, text=text[:4000], disable_web_page_preview=True), timeout=15)
        except TelegramError as e:
            if e.retry_after:
                self._flood_until = time.monotonic() + e.retry_after
            elif "no text" in str(e).lower():  # photo wala message (bot restart ke baad): caption edit karo
                self._photos.add(key)
                try:
                    self.api.call("editMessageCaption", dict(p, caption=text[:1000]), timeout=15)
                except Exception:  # noqa: BLE001
                    pass
        except Exception:  # noqa: BLE001 (progress edit kabhi job ko nahi girana chahiye)
            pass

    def answer(self, cq_id, text="", alert=False):
        try:
            self.api.call("answerCallbackQuery", {"callback_query_id": cq_id, "text": text[:190],
                                                  "show_alert": alert}, timeout=10)
        except Exception:  # noqa: BLE001
            pass

    def stop(self):
        for j in list(self.jobs.values()):
            j.cancel.set()

    def denied(self, chat, uid):
        self.say(chat, card("🔒 Access denied", "Private bot", ["Aapko is bot ki permission nahi hai."],
                            [f"🆔 Your ID · {uid}"]))

    # ---- screens
    def welcome_text(self, name, uid):
        done = stats_get().get(str(uid), 0)
        return "\n".join([
            f"👋 <b>Hi {hx(cut(name, 24))}!</b> ✨",
            "📚 <i>Novel → EPUB converter</i>",
            SEP,
            "🔁 Main novel ke link se <b>EPUB</b> bana deta hoon — aap <b>chapter range</b> chun sakte ho, "
            "formatting aur chapter list <b>bilkul waisi hi</b> rehti hai.",
            "<blockquote>" + "\n".join([
                f"📖 Converted · {done} EPUBs",
                f"⚙️ Running · {len(self.jobs)} jobs",
                f"🚀 Speed · {WORKERS} chapters parallel",
            ]) + "</blockquote>",
            "🔗 <b>Novel ka link bhejo</b> — ya neeche se option chuno 👇",
        ])

    def welcome(self, chat, name="Friend", uid=0):
        """Naya /start message (banner ke saath). Baaki sab screens isi message me edit hoti hain."""
        text, markup = self.welcome_text(name, uid), menu_kb()
        th = getattr(self._tl, "thread", None)
        if BANNER:
            p = {"chat_id": chat, "caption": text, "parse_mode": "HTML", "reply_markup": markup}
            if th:
                p["message_thread_id"] = th
            try:
                if self._banner_id:
                    r = self.api.call("sendPhoto", dict(p, photo=self._banner_id), timeout=30)
                elif os.path.isfile(BANNER):
                    r = self.api.call("sendPhoto", dict(p, reply_markup=json.dumps(markup)),
                                      files={"photo": (os.path.basename(BANNER), Path(BANNER).read_bytes(),
                                                       "image/jpeg")}, timeout=60)
                else:  # URL ya file_id
                    r = self.api.call("sendPhoto", dict(p, photo=BANNER), timeout=30)
                self._banner_id = r["photo"][-1]["file_id"]
                self._photos.add((chat, r["message_id"]))
                return
            except (TelegramError, OSError, KeyError) as e:
                print("banner failed (text bhej raha hoon):", e, file=sys.stderr)
        self.say(chat, text, markup, thread=th)

    def status_view(self, chat, uid):
        mine = sum(1 for j in self.jobs.values() if j.chat == chat)
        text = card("📊 Status", "Bot ki halat", quote=[
            f"🆔 Your ID · {uid}",
            f"⚙️ Your jobs · {mine}",
            f"🌍 Total jobs · {len(self.jobs)}/{MAX_JOBS_TOTAL}",
            f"📖 Converted · {stats_get().get(str(uid), 0)} EPUBs",
            f"🕒 Updated · {datetime.now().strftime('%H:%M:%S')}",
        ])
        return text, nav_kb([btn("🔄 Refresh", "m:status", "primary")])

    def jobs_view(self, chat):
        mine = [j for j in list(self.jobs.values()) if j.chat == chat]
        stamp = f"🕒 Updated · {datetime.now().strftime('%H:%M:%S')}"
        refresh = [btn("🔄 Refresh", "m:jobs", "primary")]
        if not mine:
            return card("📋 My Jobs", "Abhi khali hai", ["Koi kaam nahi chal raha."], [stamp],
                        "Novel ka link bhejo 👇"), nav_kb(refresh)
        q = []
        for j in mine:
            _, pct = bar(j.done, j.total)
            q.append(f"#{j.jid} · {cut(j.title, 26)}")
            q.append(f"     {j.rng()} · {pct}% · {cut(j.name, 16)}")
        q.append(stamp)
        rows = [[btn(f"✖ Cancel #{j.jid}", f"j:{j.jid}", "danger") for j in mine[:3]]]
        if len(mine) > 1:
            rows.append([btn("🛑 Cancel all", "ca", "danger")])
        rows.append(refresh)
        return card("📋 My Jobs", f"{len(mine)} running", quote=q), nav_kb(*rows)

    # ---- link scan -> info card
    def new_session(self, chat, url, sub="Chapter list dhoondh raha hoon"):
        now = time.monotonic()
        with self.lock:
            for s in [s for s in self.sessions.values() if now - s.t > SESSION_TTL]:
                self.sessions.pop(s.sid, None)
            sess = Session(self.next_sid, chat, url)
            self.next_sid += 1
            self.sessions[sess.sid] = sess
            self.awaiting.pop(chat, None)  # purane session ka adhura input band
        sess.thread = getattr(self._tl, "thread", None)
        sess.mid = self.say(chat, card("🔍 Scanning…", sub, [cut(url, 60)]),
                            kb([btn("✖ Cancel", f"x:{sess.sid}", "danger")]), thread=sess.thread)
        return sess

    # ---- direct chapter links (ek message me kai links = chapter list, scan nahi)
    def start_direct(self, chat, matches, uid):
        """Ek message ke saare links = chapter list. Scan nahi, seedhe chapters."""
        urls, seen = [], set()
        for m in matches:
            u = m.group(0).rstrip(".,;)")
            if u not in seen:
                seen.add(u)
                urls.append(u)
        urls = urls[:MAX_CHAPTERS]
        try:
            for u in urls:
                check_public(u)
        except FetchError as e:
            self.say(chat, card("❌ Galat link", None, [str(e)], foot="Sirf http/https links bhejo"))
            return
        sess = self.new_session(chat, urls[0], sub=f"{len(urls)} links mile · info le raha hoon")
        threading.Thread(target=self.scan_direct, args=(sess, urls, uid), daemon=True).start()

    def scan_direct(self, sess, urls, uid):
        chat = sess.chat
        try:
            info = None
            try:
                dom = get_dom(urls[0], 6)
                info = book_info(dom, urls[0])
            except (FetchError, ParseError):
                pass
            if info is None:
                info = {"title": "Novel", "author": "Unknown", "lang": "en", "url": urls[0]}
            title = info.get("title") or ""
            if (not title or title == "Novel"
                    or re.match(r"(chapter|chap|ch\.?|episode|ep\.?)\s*\d", title, re.I)):
                info["title"] = guess_title(urls[0])
            if self.sessions.get(sess.sid) is not sess:
                return  # user ne cancel kar diya
            sess.info = info
            sess.uid = uid
            sess.refs = []
            for i, u in enumerate(urls, 1):
                n = chapter_no(Ref("", u))
                sess.refs.append(Ref(f"Chapter {n or i}", u, n))
            nums = [r.num for r in sess.refs]
            if None not in nums and nums != sorted(nums):
                sess.refs.sort(key=lambda r: r.num)  # ulte/uljhe order me bheje links seedhe karo
            sess.dom = None
            self.show_choice(sess)
        except Exception:  # noqa: BLE001
            traceback.print_exc()
            self.drop_session(sess)
            self.edit(chat, sess.mid, card("❌ Error", "Internal error", ["Thodi der baad try karo."]),
                      kb(), throttle=False)

    def scan(self, sess, preset, uid):
        chat = sess.chat
        try:
            check_public(sess.url)
            dom = None
            for att in range(3):  # kai links ek saath hon to pehla try fail ho sakta hai
                try:
                    dom = get_dom(sess.url, 6)
                    break
                except FetchError:
                    if att == 2:
                        raise
                    time.sleep(2 + 2 * att + random.random())
            info = book_info(dom, sess.url)
            refs = find_toc(dom, sess.url)
            if not refs:  # chapter ka link diya hoga: novel page se chapter list nikalo
                refs, toc_dom, toc_url = resolve_toc(dom, sess.url)
                if refs:
                    info = book_info(toc_dom, toc_url)  # novel ka asli naam
            if re.match(r"(chapter|chap|ch\.?|episode|ep\.?)\s*\d", info["title"], re.I):
                info["title"] = guess_title(sess.url)  # chapter page ka naam novel ka naam nahi hota
        except (FetchError, ParseError) as e:
            self.drop_session(sess)
            self.edit(chat, sess.mid, card("❌ Failed", "Link scan nahi hua", [cut(str(e), 80)], foot="Sahi link bhejo"),
                      kb(), throttle=False)
            return
        except Exception:  # noqa: BLE001
            traceback.print_exc()
            self.drop_session(sess)
            self.edit(chat, sess.mid, card("❌ Error", "Internal error", ["Thodi der baad try karo."]), kb(),
                      throttle=False)
            return
        if self.sessions.get(sess.sid) is not sess:
            return  # user ne scan ke dauran cancel kar diya
        sess.info, sess.refs, sess.dom = info, refs, dom
        sess.uid = uid
        pos = find_link_pos(refs, sess.url)  # link wala chapter list me kahan hai
        if pos:
            sess.start_at = pos  # Auto EPUB 'Started at' isi chapter se
        pref = prefs_get(uid)  # "Save as default" wali choice
        if pref.get("sel") == "cust" and len(pref.get("range") or ()) == 2:
            sess.sel, sess.custom = "cust", tuple(pref["range"])
        elif pref.get("sel"):
            sess.sel = pref["sel"]
        q = parse.parse_qs(parse.urlparse(sess.url).query)
        if not preset and (q.get("page") or q.get("p")) and refs:
            preset = (1, len(refs))  # ?page=N link = ek page ke chapters, seedha convert
        elif not preset and pref.get("sel"):  # "Save as default" wali choice -> seedha convert
            if sess.sel == "cust" and (not sess.custom or sess.custom[0] > (len(refs) or sess.custom[0])):
                sess.sel = "all"
            else:
                preset = self.sel_range(sess)
                start = find_link_pos(sess.refs, sess.url)  # link wala chapter kahan hai
                if start and start > 1:
                    preset = shift_range(preset, start, len(sess.refs))  # link wale chapter se shuru
        if preset:
            err = self.start_job(sess, uid, [self.plan_for(sess, *preset)])
            if err:
                self.drop_session(sess)
                self.edit(chat, sess.mid, card("⚠️ Ruko", None, [err]), kb(), throttle=False)
            return
        self.show_choice(sess)

    def drop_session(self, sess):
        with self.lock:
            self.sessions.pop(sess.sid, None)
            aw = self.awaiting.get(sess.chat)
            if aw and aw[0] == sess.sid:
                self.awaiting.pop(sess.chat, None)

    # ---- range helpers
    def range_for(self, sess, choice):
        """Ek choice ('all', 'r1'.., 'cust') ka (first, last) — total ke hisaab se."""
        total = len(sess.refs)
        if choice == "all":
            return 1, (min(total, MAX_CHAPTERS) if total else 0)
        if choice in ("cust", "c"):
            return sess.custom if sess.custom else None
        if choice in PRESET_MAP:
            a, b = PRESET_MAP[choice]
            return a, (min(b, total) if total else b)
        return None

    def sel_range(self, sess):
        return self.range_for(sess, sess.sel) or self.range_for(sess, "all")

    def plan_for(self, sess, first, last):
        """Ek EPUB ka plan: (first, last, custom_naam_ya_None)."""
        return (first, last, sess.names.get(f"{first}-{last}"))

    def auto_plans(self, sess):
        """Auto EPUB: Started at se shuru, har 'size' chapters ka ek EPUB."""
        total = len(sess.refs)
        size = sess.auto
        if not size or not total:
            return []
        base = sess.names.get("auto")
        plans, a = [], max(1, sess.start_at)
        while a <= total:
            b = min(a + size - 1, total)
            lo, hi = sess.refs[a - 1].num, sess.refs[b - 1].num
            if lo is None or hi is None:
                lo, hi = a, b  # TOC wali list: list ki position hi naam
            plans.append((a, b, f"{base} [ {lo}-{hi} ]" if base else None))
            a = b + 1
        return plans

    def show_choice(self, sess):
        total, info, sid = len(sess.refs), sess.info, sess.sid
        valid = {"all", "cust", *PRESET_MAP}
        if sess.sel not in valid or (sess.sel == "cust" and not sess.custom):
            sess.sel = "all"
        if total and sess.sel in PRESET_MAP and PRESET_MAP[sess.sel][0] > total:
            sess.sel = "all"
        first, last = self.sel_range(sess)

        def opt(key, label):
            on = sess.sel == key
            return btn(("◉ " if on else "") + label, f"p:{sid}:{key}", "success" if on else None)

        row1 = [opt("all", "✂️ No cut" if total else "✂️ No cut (slow)"),
                opt("r1", span_label(*PRESET_MAP["r1"])), opt("r2", span_label(*PRESET_MAP["r2"]))]
        row2 = [opt(k, span_label(*PRESET_MAP[k])) for k in ("r4", "r5", "r3")]
        row3 = [btn(f"◉ ✏️ {span_label(first, last)}", f"p:{sid}:c", "success") if sess.sel == "cust"
                else btn("✏️ Custom…", f"p:{sid}:c")]
        row4 = [btn("🤖 Auto EPUB", f"a:{sid}:open", "primary"), btn("📝 Edit name", f"n:{sid}:open", "primary")]
        row5 = [btn("Create EPUB Book", f"p:{sid}:go", "success")]
        row6 = [btn("💾 Save as default", f"p:{sid}:sv", "primary"), btn("✖ Cancel", f"x:{sid}", "danger")]
        if total:
            quote = [f"📚 Chapters · {total}", f"✍️ Author · {cut(info['author'], 24)}",
                     f"🌐 Source · {cut(_host_key(sess.url), 24)}"]
            n = last - first + 1
            pick = "No cut (all)" if (first, last) == (1, min(total, MAX_CHAPTERS)) else span_label(first, last)
            quote.append(f"🎯 Selected · {pick} ({n} chapters)")
        else:
            quote = ["⚠️ Chapter list nahi mili", "🐢 Next-link mode (slow)",
                     f"🌐 Source · {cut(_host_key(sess.url), 24)}", f"🎯 Selected · {span_label(first, last)}"]
        nm = sess.names.get(f"{first}-{last}")
        if nm:
            quote.append(f"📝 Naam · {cut(nm, 40)}")
        foot = f"Max {MAX_CHAPTERS} chapters ek EPUB me" if total > MAX_CHAPTERS else "Create EPUB Book dabao 👇"
        self.edit(sess.chat, sess.mid, card(f"📖 {cut(info['title'], 40)}", "Range chuno, phir Create dabao",
                                            quote=quote, foot=foot),
                  kb(row1, row2, row3, row4, row5, row6), throttle=False)

    def show_auto(self, sess):
        total, sid = len(sess.refs), sess.sid

        def sz(s):
            on = sess.auto == s
            return btn(("◉ " if on else "") + str(s), f"a:{sid}:s{s}", "success" if on else None)

        custom_on = bool(sess.auto) and sess.auto not in AUTO_SIZES
        cbtn = btn(f"◉ ✏️ {sess.auto}" if custom_on else "✏️ Custom", f"a:{sid}:sc",
                   "success" if custom_on else None)
        rows = [[sz(s) for s in AUTO_SIZES[:4]],
                [sz(s) for s in AUTO_SIZES[4:]] + [cbtn],
                [btn(f"▶️ Started at · {sess.start_at}", f"a:{sid}:st", "primary")],
                [btn("✅ Create Auto EPUB", f"a:{sid}:go", "success")],
                [btn("⬅ Back", f"a:{sid}:b"), btn("✖ Cancel", f"x:{sid}", "danger")]]
        if sess.auto:
            plans = self.auto_plans(sess)
            prev = ", ".join(f"{a:02d}-{b}" for a, b, _ in plans[:3]) + (" …" if len(plans) > 3 else "")
            quote = [f"📚 Chapters · {total}", f"🧩 Size · {sess.auto} chapters per EPUB",
                     f"▶️ Started at · {sess.start_at}", f"📦 EPUBs · {len(plans)}", f"👀 Preview · {prev}"]
            base = sess.names.get("auto")
            if base:
                quote.append(f"📝 Naam · {cut(base, 36)}")
            foot = "Create Auto EPUB dabao 👇"
        else:
            quote = [f"📚 Chapters · {total}", "🧩 Size · abhi nahi chuna",
                     f"▶️ Started at · {sess.start_at}"]
            foot = "Pehle size chuno (10, 20, 25…)"
        self.edit(sess.chat, sess.mid, card("🤖 Auto EPUB", "Har EPUB me kitne chapters",
                                            quote=quote, foot=foot),
                  kb(*rows), throttle=False)

    def show_names(self, sess):
        sid = sess.sid

        def nb(choice, label):
            rng = self.range_for(sess, choice)
            has = bool(rng) and f"{rng[0]}-{rng[1]}" in sess.names
            return btn(("✏️ " if has else "") + label, f"n:{sid}:{choice}", "success" if has else None)

        auto_has = "auto" in sess.names
        rows = [[nb("all", "✂️ No cut"), nb("r1", span_label(*PRESET_MAP["r1"])), nb("r2", span_label(*PRESET_MAP["r2"]))],
                [nb(k, span_label(*PRESET_MAP[k])) for k in ("r4", "r5", "r3")],
                [btn(("✏️ " if auto_has else "") + "🤖 Auto base naam", f"n:{sid}:auto",
                     "success" if auto_has else None)],
                [btn("🗑 Sab names hatao", f"n:{sid}:clr", "danger")],
                [btn("⬅ Back", f"n:{sid}:b"), btn("✖ Cancel", f"x:{sid}", "danger")]]
        quote = [f"{'🤖 Auto base' if k == 'auto' else '📝 ' + k} · {cut(v, 30)}" for k, v in sess.names.items()]
        self.edit(sess.chat, sess.mid,
                  card("📝 Edit name", "Kis EPUB ka naam badalna hai?",
                       quote=quote or ["Abhi koi naam set nahi hai"],
                       foot="Button chuno, phir naam likh ke bhejo"),
                  kb(*rows), throttle=False)

    def ask_input(self, cid, sess, chat, kind, key, title, sub, quote, foot, back):
        """Text input ka intezaar: user ka agla message is kind ke liye use hoga."""
        with self.lock:
            self.awaiting[chat] = (sess.sid, kind, key)
        self.answer(cid)
        self.edit(chat, sess.mid, card(title, sub, quote=quote, foot=foot), kb([back]), throttle=False)

    # ---- job start (limits check + thread)
    def start_job(self, sess, uid, plans):
        chat = sess.chat
        first, last = plans[0][0], plans[-1][1]
        if sess.refs and first > len(sess.refs):
            return f"Novel me sirf {len(sess.refs)} chapters hain, {first}-{last or 'end'} nahi ban sakta."
        with self.lock:
            if len(self.jobs) >= MAX_JOBS_TOTAL:
                return "Bot par abhi bahut kaam hai, thodi der baad try karo."
            if sum(1 for j in self.jobs.values() if j.chat == chat) >= MAX_JOBS_PER_CHAT:
                return f"Ek saath max {MAX_JOBS_PER_CHAT} kaam chal sakte hain."
            job = Job(self.next_id, chat, uid, sess.url, first, last, sess.mid, sess.info["title"], sess.thread)
            self.next_id += 1
            self.jobs[job.jid] = job
            self.sessions.pop(sess.sid, None)
            self.awaiting.pop(chat, None)
        job.total = (last - first + 1) if last else max(len(sess.refs) - first + 1, 0)
        self.progress(job, "Shuru ho raha hai", throttle=False)
        threading.Thread(target=self.job, args=(job, sess, plans), daemon=True).start()
        return None

    def progress(self, job, phase, done=0, total=0, rate=0.0, eta="--", throttle=True):
        job.done, job.total = done, total or job.total
        b, pct = bar(done, job.total)
        q = [f"{b} {pct}%", f"📥 Done · {done}/{job.total}", f"📑 Range · {job.rng()}"]
        if rate:
            q.append(f"⚡ {rate:.1f} ch/s · ⏳ ETA {eta}")
        self.edit(job.chat, job.mid, card(f"📖 {cut(job.title, 40)}", f"Job #{job.jid} · {cut(job.name, 22)}",
                                          [f"⚙️ {job.tag}{phase}"], q), job_kb(job), throttle=throttle)

    def finish(self, job, head, sub, rows=(), quote=(), foot=None):
        self.edit(job.chat, job.mid, card(head, sub, rows, quote, foot), kb(), throttle=False)

    # ---- messages
    def handle(self, upd):
        if "callback_query" in upd:
            self.on_callback(upd["callback_query"])
            return
        msg = upd.get("message")
        if not msg or "chat" not in msg:
            return
        # thread ID sirf asli forum topic me use hota hai (normal group reply me bhejne se error aata tha)
        self._tl.thread = msg.get("message_thread_id") if msg.get("is_topic_message") else None
        private = msg["chat"].get("type") == "private"
        chat, frm = msg["chat"]["id"], (msg.get("from") or {})
        uid, name = frm.get("id", 0), frm.get("first_name") or "Friend"
        text = (msg.get("text") or "").strip()
        if not text:
            return
        parts = text.split()
        cmd = parts[0].split("@")[0].lower()
        if cmd == "/myid":
            self.say(chat, card("🆔 Your ID", None, quote=[str(uid)]))
            return
        if self.allowed and uid not in self.allowed:
            if private:  # group me har kisi ke message par 'Access denied' spam nahi
                self.denied(chat, uid)
            return
        if cmd in ("/start", "/menu"):
            self.welcome(chat, name, uid)
            return
        if cmd == "/help":
            self.say(chat, HELP_CARD, nav_kb())
            return
        if cmd == "/resetdefault":
            prefs_save(uid, {})
            self.say(chat, card("♻️ Default reset", "Ab har link par range screen aayegi"))
            return
        if cmd == "/status":
            self.say(chat, *self.status_view(chat, uid))
            return
        if cmd == "/jobs":
            self.say(chat, *self.jobs_view(chat))
            return
        if cmd == "/cancel":
            arg = parts[1].lstrip("#") if len(parts) > 1 else ""
            mine = [j for j in list(self.jobs.values()) if j.chat == chat]
            if arg.isdigit():
                mine = [j for j in mine if j.jid == int(arg)]
            if not mine:
                self.say(chat, card("ℹ️ Info", None, ["Aisa koi kaam nahi chal raha."]))
                return
            for j in mine:
                j.cancel.set()
            self.say(chat, card("🛑 Cancelling", None, quote=[", ".join(f"#{j.jid}" for j in mine)]))
            return

        matches = list(URL_RE.finditer(text))
        # agar bot kisi cheez ka intezaar kar raha hai (range / naam / size / start) to ye text wahi hai
        aw = self.awaiting.get(chat)
        if not matches and aw:
            sid, kind, key = aw
            sess = self.sessions.get(sid)
            if sess is None or sess.info is None:
                self.awaiting.pop(chat, None)
            else:
                self.handle_input(chat, sess, kind, key, text)
                return
        # 2 ya zyada alag links ek message me = chapter list (scan nahi, seedhe chapters)
        uniq = {m.group(0).rstrip(".,;)") for m in matches}
        # kai links tabhi 'chapter list' maane jayenge jab zyadatar me chapter number ho;
        # warna har link alag novel hai (alag-alag EPUB, har link ke baad apni range)
        if len(uniq) >= 2 and sum(1 for u in uniq if chapter_no(Ref("", u)) is not None) >= 0.8 * len(uniq):
            self.start_direct(chat, matches, uid)
            return
        if not matches:
            if private:  # group me normal baat-cheet par jawab nahi
                self.say(chat, card("🔗 Link chahiye", "Novel ka http/https link bhejo", foot="/help dekho"),
                         menu_kb())
            return
        for i, m in enumerate(matches):
            url = m.group(0).rstrip(".,;)")
            end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
            r = RANGE_RE.search(text[m.end():end])  # sirf is link ke baad wala hissa
            preset = None
            if r:
                first, last = max(int(r.group(1)), 1), int(r.group(2) or 0)
                if last and last < first:
                    self.say(chat, card("⚠️ Range galat hai", None, [f"{first}-{last}", "Ye link chhod diya."]))
                    continue
                preset = (first, last)
            sess = self.new_session(chat, url)
            threading.Thread(target=self.scan, args=(sess, preset, uid), daemon=True).start()

    def handle_input(self, chat, sess, kind, key, text):
        """Jo text user ne bheja wo kis cheez ke liye tha (range / naam / auto size / start episode)."""
        total = len(sess.refs)
        if kind == "range":
            rng, err = parse_range(text, total)
            if err:
                self.say(chat, card("⚠️ Range galat hai", None, [err], foot="Example · 1-20"))
                return
            sess.sel, sess.custom = "cust", rng
            self.awaiting.pop(chat, None)
            self.show_choice(sess)
            return
        if kind == "name":
            val = text.strip()
            if val in ("-", "reset"):
                sess.names.pop(key, None)
            else:
                sess.names[key] = val[:120]
            self.awaiting.pop(chat, None)
            self.show_names(sess)
            return
        if kind == "total":
            m = re.fullmatch(r"\s*(\d+)\s*", text)
            n = int(m.group(1)) if m else 0
            if n < 1 or n > MAX_CHAPTERS:
                self.say(chat, card("⚠️ Galat number", None, [f"1 se {MAX_CHAPTERS} ke beech likho"],
                                    foot="Example · 120"))
                return
            refs = synth_refs(sess.url, n)
            if not refs:
                self.awaiting.pop(chat, None)
                self.say(chat, card("❌ List nahi bani", None, ["Link me chapter number nahi mila."]))
                return
            sess.refs = refs
            cur = chapter_no(Ref("", sess.url)) or 1
            sess.start_at = min(max(cur, 1), n)
            self.awaiting.pop(chat, None)
            self.show_auto(sess)
            return
        if kind in ("start", "asize"):
            m = re.fullmatch(r"\s*(\d+)\s*", text)
            if not m:
                self.say(chat, card("⚠️ Sirf number likho", None, [text[:40]], foot="Example · 31"))
                return
            n = int(m.group(1))
            if kind == "start":
                if n < 1 or (total and n > total):
                    self.say(chat, card("⚠️ Galat episode", None,
                                        [f"1 se {total} ke beech number likho"]))
                    return
                sess.start_at = n
            else:
                if n < 1 or n > MAX_CHAPTERS:
                    self.say(chat, card("⚠️ Galat size", None, [f"1 se {MAX_CHAPTERS} ke beech likho"]))
                    return
                sess.auto = n
            self.awaiting.pop(chat, None)
            self.show_auto(sess)

    # ---- button presses
    def _sess_for(self, cid, rest, chat):
        sid, _, choice = rest.partition(":")
        sess = self.sessions.get(int(sid)) if sid.isdigit() else None
        if sess is None or sess.chat != chat or sess.info is None:
            self.answer(cid, "Ye session purana ho gaya. Link dobara bhejo.", True)
            return None, ""
        sess.t = time.monotonic()
        return sess, choice

    def on_callback(self, cq):
        cid, frm = cq["id"], (cq.get("from") or {})
        uid, name = frm.get("id", 0), frm.get("first_name") or "Friend"
        msg = cq.get("message") or {}
        self._tl.thread = msg.get("message_thread_id") if msg.get("is_topic_message") else None
        chat, mid = (msg.get("chat") or {}).get("id"), msg.get("message_id")
        data = cq.get("data") or ""
        if chat is None:
            self.answer(cid)
            return
        if self.allowed and uid not in self.allowed:
            self.answer(cid, "Permission nahi hai", True)
            return
        kind, _, rest = data.partition(":")
        if kind == "m":  # menu: isi message me edit hota hai (naya message nahi)
            self.answer(cid)
            if rest == "close":
                try:
                    self.api.call("deleteMessage", {"chat_id": chat, "message_id": mid}, timeout=10)
                except TelegramError:
                    self.edit(chat, mid, card("✖ Closed", None, ["Naya link bhejo ya /start dabao."]), kb(),
                              throttle=False)
                return
            if rest == "status":
                text, markup = self.status_view(chat, uid)
            elif rest == "jobs":
                text, markup = self.jobs_view(chat)
            elif rest == "help":
                text, markup = HELP_CARD, nav_kb()
            else:
                text, markup = self.welcome_text(name, uid), menu_kb()
            self.edit(chat, mid, text, markup, throttle=False)
        elif kind == "j":  # cancel job
            job = self.jobs.get(int(rest)) if rest.isdigit() else None
            if job is None or job.chat != chat:
                self.answer(cid, "Ye kaam pehle hi khatam ho chuka hai")
                return
            job.cancel.set()
            self.answer(cid, f"#{job.jid} cancel ho raha hai...")
        elif kind == "ca":  # cancel all
            mine = [j for j in list(self.jobs.values()) if j.chat == chat]
            for j in mine:
                j.cancel.set()
            self.answer(cid, f"{len(mine)} kaam cancel ho rahe hain" if mine else "Koi kaam nahi chal raha")
        elif kind == "x":  # cancel session
            sess = self.sessions.get(int(rest)) if rest.isdigit() else None
            self.answer(cid, "Cancel ho gaya")
            if sess is not None and sess.chat == chat:
                self.drop_session(sess)
                self.edit(chat, sess.mid, card("🚫 Cancelled", None, ["Naya link bhej sakte ho."]), kb(),
                          throttle=False)
        elif kind in ("p", "a", "n"):
            sess, choice = self._sess_for(cid, rest, chat)
            if sess is None:
                return
            if kind == "p":
                self._on_range(cid, sess, choice, uid, chat)
            elif kind == "a":
                self._on_auto(cid, sess, choice, uid, chat)
            else:
                self._on_names(cid, sess, choice, chat)
        else:
            self.answer(cid)

    def _on_range(self, cid, sess, choice, uid, chat):
        total = len(sess.refs)
        if choice == "c":  # Custom range likho
            quote = [f"Total chapters · {total}"] if total else ["1-20", "55-60", "100-  (100 se aakhir tak)"]
            self.ask_input(cid, sess, chat, "range", None, "✍️ Custom Range", "Range likh ke bhejo",
                           quote, "Example · 55-60", btn("⬅ Back", f"p:{sess.sid}:b"))
        elif choice == "b":
            self.awaiting.pop(chat, None)
            self.answer(cid)
            self.show_choice(sess)
        elif choice == "go":
            err = self.start_job(sess, uid, [self.plan_for(sess, *self.sel_range(sess))])
            self.answer(cid, err or "Shuru ho gaya ✅", bool(err))
        elif choice == "sv":
            pref = {"sel": sess.sel}
            if sess.sel == "cust" and sess.custom:
                pref["range"] = list(sess.custom)
            prefs_save(uid, pref)
            self.answer(cid, "💾 Default save ho gaya")
        elif choice in PRESET_MAP and total and PRESET_MAP[choice][0] > total:
            self.answer(cid, f"Novel me sirf {total} chapters hain, {PRESET_MAP[choice][0]} se range nahi ban sakti", True)
        elif choice == "all" or choice in PRESET_MAP:
            sess.sel = choice
            self.awaiting.pop(chat, None)
            self.answer(cid)
            self.show_choice(sess)
        else:
            self.answer(cid)

    def _on_auto(self, cid, sess, choice, uid, chat):
        total = len(sess.refs)
        if choice == "open":  # Auto EPUB screen kholo
            if not total:
                if chapter_no(Ref("", sess.url)) is None:
                    self.answer(cid, "Chapter list nahi mili aur link me chapter number bhi nahi hai", True)
                    return
                self.ask_input(cid, sess, chat, "total", None, "📚 Total chapters likho",
                               "Novel me kul kitne chapters hain?",
                               ["Site se chapter list nahi mili", "Link ke pattern se list banegi"],
                               f"Example · 120  (1 se {MAX_CHAPTERS})", btn("⬅ Back", f"a:{sess.sid}:b"))
                return
            self.awaiting.pop(chat, None)
            self.answer(cid)
            self.show_auto(sess)
        elif choice == "b":
            self.awaiting.pop(chat, None)
            self.answer(cid)
            self.show_choice(sess)
        elif choice == "sc":  # custom size
            self.ask_input(cid, sess, chat, "asize", None, "🧩 Chapter size likho",
                           "Kitne chapters ka ek EPUB ho?", [f"Abhi · {sess.auto or 'nahi chuna'}"],
                           f"Example · 15  (1 se {MAX_CHAPTERS})", btn("⬅ Back", f"a:{sess.sid}:open"))
        elif choice == "st":  # started at
            self.ask_input(cid, sess, chat, "start", None, "▶️ Started at likho",
                           "Kis episode se shuru karein?", [f"Abhi · {sess.start_at}", f"Total · {total}"],
                           "Example · 31", btn("⬅ Back", f"a:{sess.sid}:open"))
        elif choice == "go":
            if not sess.auto:
                self.answer(cid, "Pehle chapter size chuno (10, 20…)", True)
                return
            plans = self.auto_plans(sess)
            if not plans:
                self.answer(cid, "Started at novel ke chapters se bahar hai", True)
                return
            err = self.start_job(sess, uid, plans)
            self.answer(cid, err or f"Auto EPUB shuru ✅ ({len(plans)} EPUB)", bool(err))
        elif choice.startswith("s") and choice[1:].isdigit():
            sess.auto = int(choice[1:])
            self.answer(cid)
            self.show_auto(sess)
        else:
            self.answer(cid)

    def _on_names(self, cid, sess, choice, chat):
        total = len(sess.refs)
        if choice == "open":
            self.awaiting.pop(chat, None)
            self.answer(cid)
            self.show_names(sess)
        elif choice == "b":
            self.awaiting.pop(chat, None)
            self.answer(cid)
            self.show_choice(sess)
        elif choice == "clr":
            sess.names.clear()
            self.answer(cid, "Sab naam hat gaye")
            self.show_names(sess)
        elif choice == "auto":
            self.ask_input(cid, sess, chat, "name", "auto", "📝 Auto base naam likho",
                           "Har EPUB ka naam isse shuru hoga",
                           [f"Abhi · {sess.names.get('auto') or 'default'}", "Example · NAAM [ 31-40 ]"],
                           "Naam bhejo · '-' bhejo to default", btn("⬅ Back", f"n:{sess.sid}:open"))
        elif choice == "all" or choice in PRESET_MAP:
            rng = self.range_for(sess, choice)
            if rng is None or (total and rng[0] > total):
                self.answer(cid, "Ye range is novel me nahi hai", True)
                return
            key = f"{rng[0]}-{rng[1]}"
            self.ask_input(cid, sess, chat, "name", key, "📝 EPUB naam likho",
                           f"{'No cut' if choice == 'all' else span_label(*rng)} ka naam",
                           [f"Abhi · {sess.names.get(key) or 'default'}"],
                           "Naam bhejo · '-' bhejo to default", btn("⬅ Back", f"n:{sess.sid}:open"))
        else:
            self.answer(cid)

    # ---- ek novel ka poora kaam (ek ya zyada EPUB)
    def job(self, job, sess, plans):
        chat, url, cancel = job.chat, job.url, job.cancel
        tmp = Path(tempfile.mkdtemp(prefix="epub"))
        try:
            info, refs, dom = dict(sess.info), sess.refs, sess.dom
            sess.dom = None
            q = parse.parse_qs(parse.urlparse(url).query)
            page_link = bool(q.get("page") or q.get("p"))
            n_plans = len(plans)
            epubs, all_chapters = 0, 0
            for k, (first, last, custom) in enumerate(plans, 1):
                if cancel.is_set():
                    raise Cancelled()
                job.tag = f"[{k}/{n_plans}] " if n_plans > 1 else ""
                if refs:
                    full_n = len(refs)
                    seg = refs[first - 1:(last or full_n)][:MAX_CHAPTERS]
                    if not seg:
                        raise ParseError("Is range me koi chapter nahi hai")
                    if page_link:
                        label = range_label(seg, url, first, full_n)
                    elif seg[0].num is not None and seg[-1].num is not None:
                        label = f"[ {seg[0].num}-{seg[-1].num} ]"  # links ke asli chapter numbers
                    else:
                        label = f"[ {first}-{first + len(seg) - 1} ]"
                    job.first, job.last = first, first + len(seg) - 1
                    chapters = self._download_all(seg, job)
                else:
                    chapters = self._crawl(dom, url, first, last, job)
                    label = f"[ {first}-{first + len(chapters) - 1} ]" if chapters else f"[ {first}- ]"
                if not chapters:
                    raise ParseError("Koi chapter nahi mila. Chapter ya novel ka sahi link bhejo.")

                name = ascii_clean(info["title"]) or info["title"]
                m = re.search(r"\d+", label)
                base = int(m.group()) if m else first

                def make_title(a, b, whole, _label=label, _custom=custom, _name=name):
                    if _custom:
                        return _custom if whole else f"{_custom} [ {a}-{b} ]"  # split parts ke naam alag
                    return f"{_label} {_name}" if whole else f"[ {a}-{b} ] {_name}"

                self.progress(job, "EPUB ban rahi hai", len(chapters), len(chapters), throttle=False)
                parts = self._pack_parts(info, chapters, base, tmp, make_title)
                bad = [c for c in chapters if not c.ok]
                all_chapters += len(chapters)
                self.progress(job, "Telegram par bhej raha hoon", len(chapters), len(chapters), throttle=False)
                for i, (path, title, cnt, size) in enumerate(parts, 1):
                    sub = f"Job #{job.jid}"
                    if n_plans > 1:
                        sub += f" · {k}/{n_plans}"
                    if len(parts) > 1:
                        sub += f" · Part {i}/{len(parts)}"
                    cap = card(f"📚 {cut(title, 60)}", sub,
                               quote=[f"📚 Chapters · {cnt}", f"💾 Size · {size / 1048576:.1f} MB"],
                               foot="Happy reading 📖")
                    self.upload(chat, path, tg_filename(safe_filename(title, 120)) + ".epub", cap, job.thread)
                    stats_add(job.uid)
                    epubs += 1
                if bad:
                    self.say(chat, card(f"⚠️ #{job.jid} · {len(bad)} chapters fail", "Site se nahi aaye",
                                        quote=[cut(c.title, 40) for c in bad[:20]], foot="Wahi range dobara bhejo"),
                             thread=job.thread)
            job.tag = ""
            try:  # status card hata do, taaki EPUB seedha link ke neeche dikhe
                self.api.call("deleteMessage", {"chat_id": chat, "message_id": job.mid}, timeout=10)
            except Exception:  # noqa: BLE001
                self.finish(job, "✅ Completed", f"Job #{job.jid}", [f"📖 {cut(job.title, 50)}"],
                            [f"📚 EPUBs · {epubs}", f"📚 Chapters · {all_chapters}"])
        except Cancelled:
            self.finish(job, "🚫 Cancelled", f"Job #{job.jid}", ["Kaam rok diya gaya."])
        except (FetchError, ParseError) as e:
            self.finish(job, "❌ Failed", f"Job #{job.jid}", [cut(str(e), 90)])
        except TelegramError as e:
            print("send failed:", e, file=sys.stderr)
            self.finish(job, "❌ Send failed", f"Job #{job.jid}", ["Telegram par file nahi gayi.", "Dobara try karo."])
        except Exception:  # noqa: BLE001
            traceback.print_exc()
            self.finish(job, "❌ Error", f"Job #{job.jid}", ["Internal error.", "Thodi der baad try karo."])
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
            self._last_edit.pop((chat, job.mid), None)
            with self.lock:
                self.jobs.pop(job.jid, None)

    def _pack_parts(self, info, chapters, base, tmp, make_title):
        """EPUB banao. 49MB se badi ho to chapters barabar hisso me baant ke kai EPUB."""
        whole = make_title(base, base + len(chapters) - 1, True)
        out = pack_epub(dict(info, title=whole), chapters, tmp / "book.epub")
        size = out.stat().st_size
        if size <= TG_LIMIT:
            return [(out, whole, len(chapters), size)]
        n = int(size / (TG_LIMIT * 0.85)) + 1
        per = -(-len(chapters) // n)
        res = []
        for k in range(n):
            sub = chapters[k * per:(k + 1) * per]
            if not sub:
                break
            a = base + k * per
            b = a + len(sub) - 1
            title = make_title(a, b, False)
            path = pack_epub(dict(info, title=title), sub, tmp / f"part{k + 1}.epub")
            sz = path.stat().st_size
            if sz > TG_LIMIT:
                raise ParseError("EPUB bahut badi hai. Chhoti range chuno, jaise 1-500")
            res.append((path, title, len(sub), sz))
        out.unlink(missing_ok=True)
        return res

    def upload(self, chat, path, fname, caption, thread=None):
        """EPUB bhejo: retry + flood wait. Ek saath max 3 uploads (bandwidth/RAM)."""
        last = None
        with _UPLOAD_SEM:
            for attempt in range(4):
                params = {"chat_id": chat, "caption": caption, "parse_mode": "HTML"}
                if attempt >= 2:  # caption HTML ki wajah se reject ho to simple caption
                    params = {"chat_id": chat, "caption": _TAG_STRIP.sub("", caption)[:1000]}
                if thread:
                    params["message_thread_id"] = thread  # file usi topic me jayegi
                try:
                    return self.api.upload("sendDocument", params, "document", path, fname, "application/epub+zip")
                except TelegramError as e:
                    last = e
                    print("upload retry:", e, file=sys.stderr)
                    if thread and "thread" in str(e).lower():
                        thread = None  # topic nahi mila -> General me bhejo
                    time.sleep(min(e.retry_after, 30) + 1 if e.retry_after else 2 * (attempt + 1))
        raise last

    def _run_batch(self, refs, idxs, results, tries, phase, job):
        """Daemon worker threads queue se chapters uthate hain."""
        q = queue.Queue()
        for i in idxs:
            q.put(i)
        total, done, lk, t0 = q.qsize(), [0], threading.Lock(), time.monotonic()
        cancel = job.cancel

        def worker():
            while not cancel.is_set():
                try:
                    i = q.get_nowait()
                except queue.Empty:
                    return
                try:
                    results[i] = fetch_chapter(refs[i], tries, cancel, job.title)
                except Exception as e:  # noqa: BLE001
                    results[i] = _failed(refs[i].title, e)
                with lk:
                    done[0] += 1

        threads = [threading.Thread(target=worker, daemon=True) for _ in range(min(WORKERS, total))]
        for t in threads:
            t.start()
        while any(t.is_alive() for t in threads):
            d, el = done[0], time.monotonic() - t0
            rate = d / el if el > 1 else 0.0
            self.progress(job, phase, d, total, rate, _fmt((total - d) / rate) if rate > 0 else "--")
            time.sleep(1)

    def _download_all(self, refs, job):
        n = len(refs)
        results = [None] * n
        lim = get_limiter(refs[0].url)
        job.total = n
        self._run_batch(refs, range(n), results, CH_TRIES, "Downloading", job)
        mark_dupes(results)
        for p in range(1, REPAIR_PASSES + 1):  # fail wale chapters ko dheere dobara try karo
            if job.cancel.is_set():
                break
            bad = [i for i, c in enumerate(results) if c is None or not c.ok]
            if not bad:
                break
            lim.cap(max(MIN_WORKERS, WORKERS // 2))
            self.progress(job, f"{len(bad)} fail, retry {p}/{REPAIR_PASSES}", n - len(bad), n, throttle=False)
            time.sleep(2 * p)
            self._run_batch(refs, bad, results, CH_TRIES + 1, f"Retry round {p}", job)
            mark_dupes(results)
        if job.cancel.is_set():
            raise Cancelled()
        return [c or _failed(refs[i].title, "pata nahi kyun") for i, c in enumerate(results)]

    def _crawl(self, dom, url, first, last, job):
        """Chapter list na mile to 'Next' link follow karo (ek-ek karke)."""
        cur = url
        if not find_next(dom, url):
            ff = find_first_chapter(dom, url)
            if ff:
                cur, dom = ff, None
        chapters, seen, idx = [], set(), 0
        limit = min(last or MAX_CHAPTERS, first + MAX_CHAPTERS - 1)
        job.total = max(limit - first + 1, 1)
        while cur and cur not in seen and idx < limit:
            if job.cancel.is_set():
                raise Cancelled()
            seen.add(cur)
            try:
                d = dom if dom is not None else get_dom(cur)
            except FetchError:
                if chapters:
                    break
                raise
            dom = None
            idx += 1
            if idx >= first:
                chapters.append(make_chapter(page_title(d) or f"Chapter {idx}", d, job.title))
                self.progress(job, "Downloading (slow mode)", len(chapters), job.total)
            cur = find_next(d, cur)
        return chapters

    # ---- main loop
    def run(self):
        me = self.api.call("getMe")
        try:
            self.api.call("deleteWebhook")
        except TelegramError:
            pass
        try:
            self.api.call("setMyCommands", {"commands": [
                {"command": "start", "description": "Bot shuru karo"},
                {"command": "help", "description": "Guide dekho"},
                {"command": "jobs", "description": "Chalte kaam dekho"},
                {"command": "status", "description": "Bot status"},
                {"command": "resetdefault", "description": "Saved default hatao"},
                {"command": "cancel", "description": "Kaam rok do"},
                {"command": "myid", "description": "Apna Telegram ID"}]})
        except TelegramError:
            pass
        offset = None
        try:  # purane pending messages skip karo
            old = self.api.call("getUpdates", {"offset": -1, "timeout": 0})
            if old:
                offset = old[-1]["update_id"] + 1
        except TelegramError:
            pass
        print(f"Bot @{me.get('username')} chal raha hai. Workers/job: {WORKERS}, max jobs: {MAX_JOBS_TOTAL}. "
              f"Allowed: {sorted(self.allowed) or 'sab log'}", flush=True)
        print("Telegram me bot kholo aur /start bhejo. Rokne ke liye Stop dabao.", flush=True)
        backoff = 1
        while True:
            params = {"timeout": 25, "allowed_updates": ["message", "callback_query"]}
            if offset is not None:
                params["offset"] = offset
            try:
                updates = self.api.call("getUpdates", params, timeout=35)
                backoff = 1
            except TelegramError as e:
                wait = e.retry_after or backoff
                print("getUpdates:", e, f"(wait {wait}s)", file=sys.stderr, flush=True)
                time.sleep(wait)
                backoff = min(backoff * 2, 15)
                continue
            for u in updates if isinstance(updates, list) else []:
                offset = u["update_id"] + 1
                try:
                    self.handle(u)
                except Exception:  # noqa: BLE001
                    traceback.print_exc()


# ============================== RENDER (free Web Service) ==============================
# Render free Web Service ko ek port par HTTP jawab chahiye, warna deploy fail hota hai.
# Free service 15 min bina request ke so jati hai -> khud ko ping karte rehte hain (RENDER_EXTERNAL_URL).
def start_web():
    from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

    class H(BaseHTTPRequestHandler):
        def _ok(self, body=True):
            data = b"Novel EPUB bot is running"
            self.send_response(200)
            self.send_header("Content-Type", "text/plain; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            if body:
                self.wfile.write(data)

        def do_GET(self):
            self._ok()

        def do_HEAD(self):
            self._ok(False)

        def log_message(self, *a):
            pass

    port = int(os.environ.get("PORT") or 10000)
    srv = ThreadingHTTPServer(("0.0.0.0", port), H)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    print(f"Web server port {port} par chal raha hai", flush=True)

    url = (os.environ.get("RENDER_EXTERNAL_URL") or os.environ.get("SELF_URL") or "").strip()
    if url:
        def pinger():
            while True:
                time.sleep(600)  # 10 min
                try:
                    request.urlopen(request.Request(url, headers={"User-Agent": "keepalive"}), timeout=20).read(64)
                except Exception:  # noqa: BLE001
                    pass
        threading.Thread(target=pinger, daemon=True).start()


def main():
    token = (os.environ.get("BOT_TOKEN") or os.environ.get("TELEGRAM_BOT_TOKEN") or BOT_TOKEN).strip()
    if not re.fullmatch(r"\d{5,}:[A-Za-z0-9_-]{10,}", token):
        print("Bot token galat/khali hai. Render > Environment me BOT_TOKEN daalo (format 123456789:AA...).",
              file=sys.stderr)
        return 2
    allowed = set(ALLOWED_USERS) | {int(x) for x in re.findall(r"\d+", os.environ.get("ADMIN_ID", "")
                                                                 + " " + os.environ.get("ALLOWED_USERS", ""))}
    if not allowed:  # public bot na ban jaye
        print("ADMIN_ID khali hai. Render > Environment me ADMIN_ID daalo (apna Telegram ID, /myid se milta hai).",
              file=sys.stderr)
        return 2
    start_web()
    bot = Bot(TelegramAPI(token), allowed)
    try:
        bot.run()
    except KeyboardInterrupt:
        print("\nStopped.")
        bot.stop()
    except TelegramError as e:
        print(f"Start nahi hua: {e} (token aur internet check karo)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())