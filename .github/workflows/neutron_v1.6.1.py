#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Neutron - Portable Web Browser
PyQt6 + QtWebEngine (Chromium)
ข้อมูลทั้งหมดอยู่ใน ./UserData ข้างไฟล์ .py / .exe
"""
from __future__ import annotations

import argparse
import base64
import html
import io
import itertools
import json
import logging
import os
import re
import shutil
import sqlite3
import sys
import time
import zipfile
import threading
import urllib.request
import urllib.error
import mimetypes
import uuid
import ipaddress
import socket
import hashlib
import faulthandler
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import unquote
from functools import partial, lru_cache
from pathlib import Path
from string import Template
from typing import Optional

# ============================================================
# 1) Portable paths + logging + config  (ก่อนสร้าง QApplication)
# ============================================================
APP_NAME = "Neutron"
APP_VERSION = "1.6.0"


def app_dir() -> Path:
    """Directory containing the executable/source file (not PyInstaller's temp dir)."""
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def resource_path(*names) -> Optional[Path]:
    """Find bundled resources in source, onedir, or onefile builds."""
    roots = []
    meipass = getattr(sys, "_MEIPASS", None)
    if meipass:
        roots.append(Path(meipass))
    roots.extend((app_dir(), Path(__file__).resolve().parent))
    seen = set()
    for root in roots:
        try:
            key = str(root.resolve())
        except OSError:
            key = str(root)
        if key in seen:
            continue
        seen.add(key)
        for name in names:
            candidate = root / name
            if candidate.is_file():
                return candidate
    return None


def load_app_icon() -> QIcon:
    path = resource_path("neutron.ico", "Neutron.ico", "icon.ico", "app.ico")
    if path:
        icon = QIcon(str(path))
        if not icon.isNull():
            return icon
    if getattr(sys, "frozen", False):
        try:
            icon = QFileIconProvider().icon(QFileInfo(sys.executable))
            if not icon.isNull():
                return icon
        except Exception:
            log.exception("Could not load executable icon")
    return QIcon()


_SECOND_LEVEL = {"co", "com", "net", "org", "gov", "edu", "ac", "go", "or", "in", "ne"}


@lru_cache(maxsize=4096)
def base_domain(host: str) -> str:
    host = (host or "").strip(".").lower()
    parts = host.split(".")
    if len(parts) <= 2:
        return host
    if len(parts[-1]) == 2 and parts[-2] in _SECOND_LEVEL:
        return ".".join(parts[-3:])
    return ".".join(parts[-2:])


def host_suffixes(host: str):
    parts = (host or "").split(".")
    for i in range(len(parts)):
        yield ".".join(parts[i:])


def split_url(url_l: str):
    """Fast host extraction from an already-lowercase URL, without constructing QUrl."""
    i = url_l.find("://")
    if i < 0:
        return "", 0
    start, end = i + 3, len(url_l)
    for ch in "/?#":
        j = url_l.find(ch, start)
        if j >= 0 and j < end:
            end = j
    authority = url_l[start:end]
    at = authority.rfind("@")
    if at >= 0:
        start += at + 1
        authority = authority[at + 1:]
    if authority.startswith("["):
        close = authority.find("]")
        host = authority[:close + 1] if close >= 0 else authority
    else:
        colon = authority.find(":")
        host = authority[:colon] if colon >= 0 else authority
    return host.rstrip("."), start + len(host)


def session_url(url: QUrl) -> str:
    """Avoid restoring internal pages as real external URLs."""
    if (url.isEmpty() or url.scheme().lower() in ("neutron", "about", "data", "blob")
            or url.host().lower() in (OCR_HOST, BG_HOST)):
        return "neutron://newtab"
    return url.toString()


def _prepare_data_dir() -> Path:
    primary = app_dir() / "UserData"
    try:
        primary.mkdir(parents=True, exist_ok=True)
        probe = primary / ".write_test"
        probe.write_text("ok")
        probe.unlink()
        return primary
    except OSError:
        fallback = Path.home() / ".neutron" / "UserData"  # โฟลเดอร์เขียนไม่ได้ (เช่น Program Files)
        fallback.mkdir(parents=True, exist_ok=True)
        return fallback


DATA_DIR = _prepare_data_dir()
PROFILES_DIR = DATA_DIR / "Profiles"
PROFILES_DIR.mkdir(parents=True, exist_ok=True)
CONFIG_FILE = DATA_DIR / "config.json"
WIPE_MARKER = DATA_DIR / ".wipe_on_start"

logging.basicConfig(
    filename=str(DATA_DIR / "neutron.log"), level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s", encoding="utf-8",
)
log = logging.getLogger("neutron")

try:
    from PyQt6.QtCore import (
        Qt, QUrl, QTimer, QEvent, QBuffer, QByteArray, QIODevice, QObject, pyqtSignal, QThread, QFileInfo,
        QStringListModel, QStandardPaths, QT_VERSION_STR, PYQT_VERSION_STR,
    )
    from PyQt6.QtGui import QAction, QKeySequence, QFont, QFontDatabase, QDesktopServices, QImage, QPainter, QColor, QIcon
    from PyQt6.QtWidgets import (
        QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QStackedWidget, QTabBar,
        QToolButton, QPushButton, QLineEdit, QLabel, QFrame, QProgressBar, QMenu, QMessageBox,
        QInputDialog, QFileDialog, QFileIconProvider, QListWidget, QListWidgetItem, QHeaderView, QDialog, QFormLayout, QComboBox, QCheckBox, QSpinBox,
        QPlainTextEdit, QTabWidget, QTableWidget, QTableWidgetItem, QTableWidgetSelectionRange,
        QAbstractItemView, QSplitter, QCompleter,
    )
    from PyQt6.QtWebEngineCore import (
        QWebEnginePage, QWebEngineProfile, QWebEngineSettings, QWebEngineScript,
        QWebEngineUrlScheme, QWebEngineUrlSchemeHandler, QWebEngineUrlRequestJob,
        QWebEngineDownloadRequest, QWebEngineUrlRequestInterceptor, QWebEngineUrlRequestInfo,
    )
    from PyQt6.QtWebEngineWidgets import QWebEngineView
except ImportError as _e:  # pragma: no cover
    print("Missing dependency:", _e, "\nRun: pip install PyQt6 PyQt6-WebEngine cryptography")
    sys.exit(1)

try:
    from cryptography.fernet import Fernet, InvalidToken
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    from cryptography.hazmat.primitives.kdf.scrypt import Scrypt
    HAS_CRYPTO = True
except ImportError:
    HAS_CRYPTO = False

# AdBlock matching is handled by Neutron's indexed in-process engine.
# No braveblock package or external native matcher is required.
NEWTAB_URL = QUrl("neutron://newtab")
OCR_HOST = "neutron-ocr.local"
OCR_BASE_URL = f"https://{OCR_HOST}/"
BG_HOST = "neutron-bg.local"
BG_BASE_URL = f"https://{BG_HOST}/"
USER_COSMETIC_SCRIPT = "neutron-user-cosmetic"

# Search engines are compatibility-sensitive: trackers/ads on result pages may
# share endpoints with search suggestions, ranking and result rendering.
# Network and list-based cosmetic rules are therefore bypassed on these origins.
SEARCH_ENGINE_COMPAT_DOMAINS = (
    "google.com", "google.co.th", "bing.com", "duckduckgo.com",
    "search.brave.com", "search.yahoo.com", "yahoo.com", "ecosia.org",
)


def is_search_engine_host(host: str) -> bool:
    host = (host or "").lower().strip(".")
    return any(host == domain or host.endswith("." + domain)
               for domain in SEARCH_ENGINE_COMPAT_DOMAINS)


def read_json(path: Path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8-sig"))
    except (OSError, ValueError):
        return default


def write_json(path: Path, data) -> None:
    try:
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        os.replace(tmp, path)
    except OSError:
        log.exception("write_json failed: %s", path)


def safe_name(name: str) -> str:
    return re.sub(r'[\\/:*?"<>|]', "_", name).strip(" .") or "Default"


SEARCH_ENGINES = {
    "Google": "https://www.google.com/search?q={}",
    "Bing": "https://www.bing.com/search?q={}",
    "DuckDuckGo": "https://duckduckgo.com/?q={}",
    "Brave": "https://search.brave.com/search?q={}",
    "Yahoo": "https://search.yahoo.com/search?p={}",
    "Ecosia": "https://www.ecosia.org/search?q={}",
}
STARTUP_MODES = [
    ("newtab", "Open the New Tab page"),
    ("home", "Open my homepage"),
    ("restore", "Continue where I left off"),
    ("custom", "Open specific pages"),
]
DEFAULTS = {
    "last_profile": "Default", "theme": "dark", "startup_mode": "newtab",
    "homepage": "https://www.google.com/", "startup_urls": "", "search_engine": "Google",
    "accept_language": "th-TH,th;q=0.9,en-US;q=0.8,en;q=0.7",
    "font_standard": "", "font_fixed": "", "font_serif": "", "font_sans": "",
    "font_size": 16, "font_fixed_size": 13, "font_min_size": 12, "default_zoom": 100,
    "javascript": True, "popups": True, "save_passwords": True, "ask_download": True,
    "download_dir": "", "clear_on_exit": False, "force_dark_web": False,
    "show_bookmarks_bar": True, "window_geometry": "",
    # Network/cosmetic blocking is opt-in; it can affect compatibility and search pages.
    "adblock_enabled": False, "adblock_opt_in_acknowledged": False,
    "adblock_update_days": 7, "auto_suspend_minutes": 0,
    "reader_font_size": 18, "reader_theme": "light",
    "dl_categorize": True,
}

ADBLOCK_LISTS = {
    "AdGuard Base": "https://filters.adtidy.org/extension/ublock/filters/2.txt",
    "AdGuard Tracking Protection": "https://filters.adtidy.org/extension/ublock/filters/3.txt",
}
ADBLOCK_BUILTIN = """
||doubleclick.net^
||googlesyndication.com^
||googleadservices.com^
||adservice.google.com^
||pagead2.googlesyndication.com^
||adnxs.com^
||taboola.com^
||outbrain.com^
||scorecardresearch.com^
||zedo.com^
||popads.net^
||popcash.net^
"""
RIGHT_CLICK_JS = r'''(function(){
  if (window.__neutronRightClickInstalled) return;
  window.__neutronRightClickInstalled = true;
  window.__neutronForceRightClick = false;
  const original = Event.prototype.preventDefault;
  Event.prototype.preventDefault = function(){
    if (window.__neutronForceRightClick && this && this.type === 'contextmenu') return;
    return original.apply(this, arguments);
  };
  document.addEventListener('contextmenu', function(e){
    if (window.__neutronForceRightClick) {
      e.stopImmediatePropagation();
      e.returnValue = true;
    }
  }, true);
})();'''
ELEMENT_PICKER_JS = r'''(function(){
  if (window.__neutronPickerActive) return;
  window.__neutronPickerActive = true;
  const old = document.getElementById('__neutron_picker_overlay'); if(old) old.remove();
  const tip=document.createElement('div'); tip.id='__neutron_picker_overlay';
  tip.textContent='Neutron Element Picker — คลิกองค์ประกอบเพื่อ Block • Esc เพื่อยกเลิก';
  Object.assign(tip.style,{position:'fixed',zIndex:'2147483647',top:'8px',left:'50%',transform:'translateX(-50%)',padding:'9px 14px',background:'#111827',color:'#fff',border:'2px solid #60a5fa',borderRadius:'8px',font:'13px sans-serif',pointerEvents:'none'});
  document.documentElement.appendChild(tip);
  let last=null;
  function selector(el){
    if(!el||el===document.body||el===document.documentElement)return 'body';
    if(el.id)return '#'+CSS.escape(el.id);
    const parts=[]; let n=el;
    while(n&&n.nodeType===1&&n!==document.body&&parts.length<5){
      let x=n.tagName.toLowerCase(); if(n.classList&&n.classList.length){x+='.'+Array.from(n.classList).slice(0,2).map(CSS.escape).join('.');}
      const parent=n.parentElement; if(parent){const same=Array.from(parent.children).filter(c=>c.tagName===n.tagName); if(same.length>1)x+=':nth-of-type('+(same.indexOf(n)+1)+')';}
      parts.unshift(x); n=parent;
    }
    return parts.join(' > ');
  }
  function over(e){const el=e.target;if(last&&last!==el)last.style.outline=last.dataset.__nOldOutline||'';last=el;if(el&&el.style){el.dataset.__nOldOutline=el.style.outline;el.style.outline='3px solid #ff3b30';}}
  function click(e){e.preventDefault();e.stopImmediatePropagation();const el=e.target;const sel=selector(el);cleanup();console.log('__NEUTRON_BLOCK__'+JSON.stringify({selector:sel,host:location.hostname}));}
  function key(e){if(e.key==='Escape'){e.preventDefault();cleanup();}}
  function cleanup(){if(last&&last.style)last.style.outline=last.dataset.__nOldOutline||'';tip.remove();document.removeEventListener('pointerover',over,true);document.removeEventListener('click',click,true);document.removeEventListener('keydown',key,true);window.__neutronPickerActive=false;}
  document.addEventListener('pointerover',over,true);document.addEventListener('click',click,true);document.addEventListener('keydown',key,true);
})();'''



OCR_HTML = r'''<!doctype html><html lang="th"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Neutron OCR</title><style>
:root{--bg:#16181d;--s:#22252d;--s2:#2c303a;--t:#eceff4;--m:#9aa3b5;--a:#6d8dff;--b:#343946}
*{box-sizing:border-box}body{margin:0 auto;background:var(--bg);color:var(--t);font:14px "Leelawadee UI","Noto Sans Thai","Segoe UI",sans-serif;padding:24px;max-width:1100px}
h1{font-weight:300;letter-spacing:6px;margin:0 0 4px}.sub{color:var(--m);margin-bottom:18px}
#drop{border:2px dashed var(--b);border-radius:16px;padding:46px 20px;text-align:center;background:var(--s);cursor:pointer;transition:.15s}#drop.hot{border-color:var(--a);background:var(--s2)}#drop b{font-size:18px}
.row{display:flex;gap:10px;flex-wrap:wrap;align-items:center;margin:14px 0}
select,button{font:inherit;color:var(--t);background:var(--s2);border:1px solid var(--b);border-radius:8px;padding:7px 14px}button{cursor:pointer}button:hover{border-color:var(--a)}button.p{background:var(--a);border:0;color:#fff}
progress{width:100%;height:8px;accent-color:var(--a)}#status{color:var(--m);min-height:20px;margin:6px 0}
textarea{width:100%;height:46vh;min-height:260px;background:var(--s);color:var(--t);border:1px solid var(--b);border-radius:10px;padding:14px;font:15px/1.7 "Leelawadee UI","Noto Sans Thai",sans-serif;resize:vertical}
</style></head><body>
<h1>NEUTRON OCR</h1><div class="sub">ถอดข้อความจากรูปภาพและ PDF ด้วย Tesseract.js (ประมวลผลใน Browser; โหลด Engine/ข้อมูลภาษาเมื่อต้องใช้ครั้งแรก)</div>
<div id="drop"><b>วางไฟล์รูปภาพ / PDF ที่นี่</b><br><span>หรือคลิกเพื่อเลือกไฟล์ • วางรูปจากคลิปบอร์ดด้วย Ctrl+V</span></div>
<input id="file" type="file" multiple accept="image/*,.pdf,application/pdf" hidden>
<div class="row">
 <label>ภาษา <select id="lang"><option value="tha+eng">ไทย + อังกฤษ</option><option value="eng">English</option><option value="tha">ไทย</option></select></label>
 <label>ความละเอียด PDF <select id="scale"><option value="1.5">1.5</option><option value="2" selected>2</option><option value="3">3</option></select></label>
 <label><input type="checkbox" id="thai" checked> ลบช่องว่างระหว่างตัวอักษรไทย</label>
</div>
<progress id="bar" value="0" max="1"></progress><div id="status">พร้อมใช้งาน</div>
<textarea id="out" placeholder="ข้อความที่ถอดได้จะแสดงที่นี่ (แก้ไขได้)"></textarea>
<div class="row"><button class="p" id="b-txt">Save .txt</button><button class="p" id="b-md">Save .md</button><button class="p" id="b-docx">Save .docx</button><button id="b-copy">Copy</button><button id="b-clear">Clear</button></div>
<script>
const TESS='https://cdn.jsdelivr.net/npm/tesseract.js@5/dist/tesseract.min.js';
const PDFJS='https://cdn.jsdelivr.net/npm/pdfjs-dist@3.11.174/build/pdf.min.js';
const PDFW='https://cdn.jsdelivr.net/npm/pdfjs-dist@3.11.174/build/pdf.worker.min.js';
const $=s=>document.querySelector(s);let worker=null,wlang='',queue=[],busy=false;const scriptPromises=new Map();
const setStatus=t=>{$('#status').textContent=t},setProg=p=>{$('#bar').value=Math.max(0,Math.min(1,Number(p)||0));};
function loadScript(src){if(scriptPromises.has(src))return scriptPromises.get(src);const promise=new Promise((resolve,reject)=>{let s=document.querySelector('script[data-neutron-src="'+src+'"]');if(s&&s.dataset.loaded==='1'){resolve();return;}if(s)s.remove();s=document.createElement('script');s.src=src;s.dataset.neutronSrc=src;s.onload=()=>{s.dataset.loaded='1';resolve();};s.onerror=()=>{scriptPromises.delete(src);s.remove();reject(new Error('โหลดไลบรารีไม่ได้ (ต้องต่ออินเทอร์เน็ตครั้งแรก): '+src));};document.head.appendChild(s);});scriptPromises.set(src,promise);return promise;}
async function getWorker(lang){if(worker&&wlang===lang)return worker;if(worker){await worker.terminate();worker=null;}await loadScript(TESS);if(!window.Tesseract)throw new Error('Tesseract.js ไม่พร้อมใช้งาน');setStatus('กำลังโหลด OCR Engine และข้อมูลภาษา ('+lang+') ...');worker=await Tesseract.createWorker(lang,1,{logger:m=>{if(m.status==='recognizing text')setProg(m.progress);else if(m.progress!==undefined)setStatus(m.status+' '+Math.round(m.progress*100)+'%');}});wlang=lang;return worker;}
function tidy(t){if($('#thai').checked)t=t.replace(/([\u0E00-\u0E7F])[ \t]+(?=[\u0E00-\u0E7F])/g,'$1');return t.replace(/[ \t]+\n/g,'\n').trim();}
function addText(name,text){const o=$('#out');o.value+=(o.value?'\n\n':'')+'----- '+name+' -----\n\n'+text;}
async function processFile(f){if(!f)return;if(f.size>100*1024*1024)throw new Error('ไฟล์ใหญ่เกิน 100 MB');const w=await getWorker($('#lang').value);const parts=[];if(f.type==='application/pdf'||/\.pdf$/i.test(f.name)){await loadScript(PDFJS);if(!window.pdfjsLib)throw new Error('PDF.js ไม่พร้อมใช้งาน');pdfjsLib.GlobalWorkerOptions.workerSrc=PDFW;const doc=await pdfjsLib.getDocument({data:new Uint8Array(await f.arrayBuffer())}).promise;if(doc.numPages>500)throw new Error('PDF มีมากกว่า 500 หน้า ซึ่งเกินขีดจำกัดเพื่อป้องกันหน่วยความจำหมด');for(let p=1;p<=doc.numPages;p++){setStatus(f.name+' - หน้า '+p+'/'+doc.numPages);setProg((p-1)/Math.max(1,doc.numPages));const page=await doc.getPage(p),vp=page.getViewport({scale:parseFloat($('#scale').value)});const c=document.createElement('canvas');c.width=Math.ceil(vp.width);c.height=Math.ceil(vp.height);await page.render({canvasContext:c.getContext('2d'),viewport:vp}).promise;parts.push((await w.recognize(c)).data.text);c.width=0;c.height=0;}}else if(f.type.startsWith('image/')||/\.(png|jpe?g|gif|bmp|webp|tiff?)$/i.test(f.name)){setStatus(f.name);setProg(0);parts.push((await w.recognize(f)).data.text);}else throw new Error('ชนิดไฟล์ไม่รองรับ: '+f.type);addText(f.name,tidy(parts.join('\n\n')));}
async function runQueue(){if(busy)return;busy=true;let done=0;const total=queue.length;try{while(queue.length){const f=queue.shift();try{await processFile(f);}catch(e){addText(f.name,'[ERROR] '+(e&&e.message||e));setStatus('ผิดพลาด: '+f.name);}done++;setProg(done/Math.max(1,total));}}finally{busy=false;setStatus('เสร็จแล้ว');setProg(1);}}
function handle(files){for(const f of files||[])queue.push(f);if(!busy&&queue.length)runQueue();}
const drop=$('#drop');drop.onclick=()=>$('#file').click();$('#file').onchange=e=>{handle([...e.target.files]);e.target.value='';};
['dragenter','dragover'].forEach(t=>document.addEventListener(t,e=>{e.preventDefault();drop.classList.add('hot');}));['dragleave','drop'].forEach(t=>document.addEventListener(t,e=>{e.preventDefault();drop.classList.remove('hot');}));document.addEventListener('drop',e=>{e.preventDefault();handle([...(e.dataTransfer.files||[])]);});document.addEventListener('paste',e=>{const cd=e.clipboardData;let fs=[...(cd&&cd.files||[])];if(!fs.length&&cd&&cd.items)fs=[...cd.items].filter(x=>x.kind==='file').map(x=>x.getAsFile()).filter(Boolean);if(fs.length)handle(fs);});
function docText(){let t=$('#out').value;const n=(t.match(/^----- .* -----$/gm)||[]).length;if(n<=1)t=t.replace(/^----- .* -----\n*/m,'');return t.trim();}
function saveBlob(blob,name){const a=document.createElement('a'),u=URL.createObjectURL(blob);a.href=u;a.download=name;document.body.appendChild(a);a.click();setTimeout(()=>{URL.revokeObjectURL(u);a.remove();},15000);}
const stamp=()=>new Date().toISOString().slice(0,19).replace(/[:T]/g,'-');
$('#b-txt').onclick=()=>saveBlob(new Blob(['\ufeff'+docText()],{type:'text/plain;charset=utf-8'}),'ocr-'+stamp()+'.txt');
$('#b-md').onclick=()=>saveBlob(new Blob([docText().replace(/^----- (.*) -----$/gm,'## $1')],{type:'text/markdown;charset=utf-8'}),'ocr-'+stamp()+'.md');
$('#b-copy').onclick=()=>{if(navigator.clipboard&&navigator.clipboard.writeText)navigator.clipboard.writeText(docText()).then(()=>setStatus('คัดลอกแล้ว'),()=>{$('#out').select();document.execCommand('copy');});else{$('#out').select();document.execCommand('copy');}};
$('#b-clear').onclick=()=>{$('#out').value='';setProg(0);setStatus('พร้อมใช้งาน');};
const crcT=(()=>{const t=[];for(let n=0;n<256;n++){let c=n;for(let k=0;k<8;k++)c=c&1?0xEDB88320^(c>>>1):c>>>1;t[n]=c>>>0;}return t;})();
const crc32=b=>{let c=0xFFFFFFFF;for(let i=0;i<b.length;i++)c=crcT[(c^b[i])&255]^(c>>>8);return(c^0xFFFFFFFF)>>>0;};const u16=n=>[n&255,(n>>>8)&255],u32=n=>[n&255,(n>>>8)&255,(n>>>16)&255,(n>>>24)&255];
function zip(files){const enc=new TextEncoder(),chunks=[],cen=[];let off=0;for(const f of files){const nm=enc.encode(f.name),crc=crc32(f.data),sz=f.data.length;const lh=new Uint8Array([0x50,0x4b,3,4,...u16(20),...u16(0x0800),...u16(0),...u16(0),...u16(0x21),...u32(crc),...u32(sz),...u32(sz),...u16(nm.length),...u16(0)]);chunks.push(lh,nm,f.data);cen.push(new Uint8Array([0x50,0x4b,1,2,...u16(20),...u16(20),...u16(0x0800),...u16(0),...u16(0),...u16(0x21),...u32(crc),...u32(sz),...u32(sz),...u16(nm.length),...u16(0),...u16(0),...u16(0),...u16(0),...u32(0),...u32(off)]),nm);off+=lh.length+nm.length+sz;}let cs=0;for(const c of cen)cs+=c.length;return new Blob([...chunks,...cen,new Uint8Array([0x50,0x4b,5,6,0,0,0,0,...u16(files.length),...u16(files.length),...u32(cs),...u32(off),0,0])],{type:'application/vnd.openxmlformats-officedocument.wordprocessingml.document'});}
const xe=s=>s.replace(/[\x00-\x08\x0B\x0C\x0E-\x1F]/g,'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
function makeDocx(text){const F='<w:rFonts w:ascii="Tahoma" w:hAnsi="Tahoma" w:cs="Tahoma" w:eastAsia="Tahoma"/><w:sz w:val="24"/><w:szCs w:val="24"/>',paras=text.split(/\r?\n/).map(l=>{const h=l.match(/^----- (.*) -----$/);return '<w:p><w:r><w:rPr>'+(h?'<w:b/><w:bCs/>':'')+F+'</w:rPr><w:t xml:space="preserve">'+xe(h?h[1]:l)+'</w:t></w:r></w:p>';}).join(''),X='<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',enc=new TextEncoder();return zip([{name:'[Content_Types].xml',data:enc.encode(X+'<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/></Types>')},{name:'_rels/.rels',data:enc.encode(X+'<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="word/document.xml"/></Relationships>')},{name:'word/document.xml',data:enc.encode(X+'<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"><w:body>'+paras+'<w:sectPr><w:pgSz w:w="11906" w:h="16838"/><w:pgMar w:top="1440" w:right="1440" w:bottom="1440" w:left="1440" w:header="708" w:footer="708" w:gutter="0"/></w:sectPr></w:body></w:document>')}]);}
$('#b-docx').onclick=()=>saveBlob(makeDocx(docText()),'ocr-'+stamp()+'.docx');
</script></body></html>'''


BG_REMOVER_HTML = r'''
<!doctype html>
<html lang="th" data-theme="dark">
<head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Neutron Background Remover</title>
<style>
:root{--bg:#070b14;--panel:#101827;--panel2:#172033;--text:#f8fafc;--muted:#94a3b8;--border:#273449;--primary:#7c3aed;--accent:#22d3ee;--danger:#ef4444;--success:#22c55e;--input:#0b1220;--shadow:0 16px 44px #0005}
html[data-theme="light"]{--bg:#eef2ff;--panel:#fff;--panel2:#f8fafc;--text:#0f172a;--muted:#64748b;--border:#dbe3ef;--primary:#6d28d9;--accent:#0891b2;--danger:#dc2626;--success:#16a34a;--input:#f8fafc;--shadow:0 16px 44px #0f172a20}
html[data-theme="retro"]{--bg:#2b2118;--panel:#f6e7c1;--panel2:#ecd59f;--text:#362618;--muted:#765d3e;--border:#a9793b;--primary:#b34528;--accent:#186f65;--danger:#a52323;--success:#377b32;--input:#fff6dd;--shadow:7px 7px 0 #38251245}
*{box-sizing:border-box}body{margin:0;min-height:100vh;background:radial-gradient(circle at 8% 0%,color-mix(in srgb,var(--primary) 18%,transparent),transparent 34%),var(--bg);color:var(--text);font:14px "Leelawadee UI","Noto Sans Thai","Segoe UI",sans-serif}
button,input,select{font:inherit}button:disabled{opacity:.48;cursor:not-allowed}.top{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:14px 20px;border-bottom:1px solid var(--border);background:var(--panel)}h1{margin:0;font-size:20px;letter-spacing:3px;font-weight:700}.muted{color:var(--muted)}.layout{max-width:1600px;margin:auto;padding:16px;display:grid;grid-template-columns:minmax(250px,320px) minmax(320px,1fr) minmax(260px,330px);gap:14px}.panel{background:var(--panel);border:1px solid var(--border);border-radius:16px;padding:15px;box-shadow:var(--shadow);min-width:0}.drop{border:2px dashed var(--border);background:var(--panel2);border-radius:14px;padding:26px 14px;text-align:center;cursor:pointer}.drop.hot{border-color:var(--accent);background:color-mix(in srgb,var(--accent) 15%,var(--panel))}.btn{border:1px solid var(--border);border-radius:9px;padding:8px 12px;color:var(--text);background:var(--panel2);cursor:pointer}.btn:hover:not(:disabled){border-color:var(--primary)}.primary{background:linear-gradient(135deg,var(--primary),#2563eb);border:0;color:white}.danger{background:var(--danger);color:white;border:0}.row{display:flex;gap:8px;flex-wrap:wrap;align-items:center;margin:10px 0}.row>*{min-width:0}.control{width:100%;padding:8px;color:var(--text);background:var(--input);border:1px solid var(--border);border-radius:8px}.field{margin:12px 0}.field label{display:flex;justify-content:space-between;gap:8px;margin-bottom:5px;color:var(--muted);font-size:12px}.field input[type=range]{width:100%;accent-color:var(--primary)}.checker{background-color:#fff;background-image:linear-gradient(45deg,#d1d5db 25%,transparent 25%),linear-gradient(-45deg,#d1d5db 25%,transparent 25%),linear-gradient(45deg,transparent 75%,#d1d5db 75%),linear-gradient(-45deg,transparent 75%,#d1d5db 75%);background-size:24px 24px;background-position:0 0,0 12px,12px -12px,-12px 0;min-height:420px;display:grid;place-items:center;overflow:auto;border-radius:12px;padding:12px}canvas{display:block;max-width:100%;max-height:68vh;margin:auto;border-radius:8px;box-shadow:0 12px 35px #0005}progress{width:100%;height:9px;accent-color:var(--primary)}textarea{width:100%;height:70px;background:var(--input);color:var(--text);border:1px solid var(--border);border-radius:8px;padding:8px}.status{min-height:22px;color:var(--muted);font-size:12px}.hidden{display:none!important}.pill{padding:4px 9px;border-radius:20px;background:var(--panel2);font-size:11px;color:var(--muted)}.toast{position:fixed;right:16px;bottom:16px;z-index:20;max-width:380px;padding:12px 15px;border-radius:10px;color:#fff;background:#111827;box-shadow:var(--shadow)}.spin{display:inline-block;width:14px;height:14px;border:2px solid #ffffff66;border-top-color:white;border-radius:50%;animation:sp .7s linear infinite;vertical-align:middle}@keyframes sp{to{transform:rotate(360deg)}}.compare{width:100%;accent-color:var(--primary)}.section-title{font-weight:700;margin:0 0 10px}.small{font-size:11px;color:var(--muted)}@media(max-width:1050px){.layout{grid-template-columns:260px minmax(300px,1fr)}.right{grid-column:1/-1;display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:14px}}@media(max-width:700px){.layout{grid-template-columns:1fr}.right{display:block}.top{align-items:flex-start;flex-direction:column}}
</style></head>
<body>
<header class="top"><div><h1>NEUTRON BACKGROUND REMOVER</h1><div class="small">AI Background Studio · ประมวลผลภายใน Browser · Model ดาวน์โหลดเมื่อใช้ครั้งแรก</div></div><div class="row" style="margin:0"><span id="network" class="pill">Offline</span><select id="theme" class="control" style="width:auto"><option value="dark">Dark</option><option value="light">Light</option><option value="retro">Retro</option></select><button id="settings" class="btn">⚙ Settings</button></div></header>
<main class="layout">
<section class="panel">
<h2 class="section-title">1. เลือกรูปภาพ</h2><div id="drop" class="drop" tabindex="0"><div style="font-size:32px">⬆</div><b>ลากรูปมาวางที่นี่</b><div class="small">หรือคลิกเพื่อเลือกไฟล์ · Ctrl+V วางภาพ</div><div class="small">JPG, PNG, WebP, BMP · ไม่เกิน 50 MB</div></div><input id="file" type="file" accept="image/jpeg,image/png,image/webp,image/bmp" hidden>
<div id="fileInfo" class="pill hidden" style="display:block;margin-top:10px"></div>
<div class="row"><button id="remove" class="btn primary" disabled style="flex:1">ลบพื้นหลังด้วย AI</button><button id="cancel" class="btn danger hidden">ยกเลิก</button></div><progress id="progress" max="100" value="0"></progress><div id="status" class="status">พร้อมใช้งาน</div>
<div class="field"><label>ภาพต้นฉบับ / ผลลัพธ์</label><button id="compare" class="btn" disabled>Before / After</button><input id="compareRange" class="compare" type="range" min="0" max="100" value="50"></div>
<div class="small">ทางลัด: Ctrl+O เปิดรูป · Ctrl+Enter ลบพื้นหลัง · Ctrl+S ส่งออก · Ctrl+V วางรูป · R คืนค่าการปรับแต่ง</div>
</section>
<section class="panel"><div class="row" style="justify-content:space-between"><div><h2 class="section-title" style="margin:0">Workspace</h2><div id="workspaceStatus" class="small">ยังไม่ได้เลือกรูปภาพ</div></div><button id="fit" class="btn">พอดีหน้าจอ</button></div><div id="canvasWrap" class="checker"><div id="empty" class="muted" style="text-align:center">▧<br>เริ่มต้นด้วยการเลือกรูปภาพ</div><canvas id="canvas" class="hidden"></canvas></div><div class="small" id="dimensions" style="margin-top:8px"></div></section>
<section class="panel right">
<div><h2 class="section-title">2. เปลี่ยนพื้นหลัง</h2><div class="row"><button class="btn mode" data-mode="transparent">โปร่งใส</button><button class="btn mode" data-mode="color">สีพื้น</button><button class="btn mode" data-mode="gradient">Gradient</button><button class="btn mode" data-mode="image">รูปภาพ</button></div>
<div class="field"><label>สีพื้นหลัง</label><input id="bgColor" type="color" class="control" value="#ffffff"></div><div class="row"><div style="flex:1"><label class="small">Gradient A</label><input id="ga" type="color" class="control" value="#7c3aed"></div><div style="flex:1"><label class="small">Gradient B</label><input id="gb" type="color" class="control" value="#22d3ee"></div></div>
<div class="field"><label>มุม Gradient <span id="angleVal">135°</span></label><input id="angle" type="range" min="0" max="360" value="135"></div><div class="field"><label>การจัดวางภาพพื้นหลัง</label><select id="fitMode" class="control"><option value="cover">เต็มพื้นที่</option><option value="contain">เห็นภาพทั้งหมด</option><option value="stretch">ยืดเต็มพื้นที่</option></select></div><div class="field"><label>เบลอพื้นหลัง <span id="blurVal">0 px</span></label><input id="blur" type="range" min="0" max="30" value="0"></div><input id="bgFile" type="file" accept="image/*" hidden><button id="bgUpload" class="btn">อัปโหลดภาพพื้นหลัง</button></div>
<div><h2 class="section-title" style="margin-top:18px">3. ปรับแต่งวัตถุ</h2>
<div class="field"><label>ขนาด <span id="scaleVal">100%</span></label><input id="scale" type="range" min="10" max="250" value="100"></div><div class="field"><label>ตำแหน่งแนวนอน <span id="xVal">0%</span></label><input id="ox" type="range" min="-100" max="100" value="0"></div><div class="field"><label>ตำแหน่งแนวตั้ง <span id="yVal">0%</span></label><input id="oy" type="range" min="-100" max="100" value="0"></div>
<div class="field"><label>Brightness <span id="brightVal">100%</span></label><input id="bright" type="range" min="0" max="200" value="100"></div><div class="field"><label>Contrast <span id="contrastVal">100%</span></label><input id="contrast" type="range" min="0" max="200" value="100"></div><div class="field"><label>Saturation <span id="satVal">100%</span></label><input id="sat" type="range" min="0" max="250" value="100"></div><div class="field"><label>ความทึบ <span id="opacityVal">100%</span></label><input id="opacity" type="range" min="0" max="100" value="100"></div><div class="field"><label>ความฟุ้งของเงา <span id="shadowVal">0 px</span></label><input id="shadow" type="range" min="0" max="80" value="0"></div><div class="field"><label>ความเข้มเงา <span id="shadowOpacityVal">35%</span></label><input id="shadowOpacity" type="range" min="0" max="100" value="35"></div><button id="resetAdjust" class="btn">คืนค่าการปรับแต่ง</button></div>
<div><h2 class="section-title" style="margin-top:18px">4. ส่งออก</h2><div class="row"><div style="flex:1"><label class="small">รูปแบบ</label><select id="format" class="control"><option value="png">PNG</option><option value="jpeg">JPG</option><option value="webp">WebP</option></select></div><div style="flex:1"><label class="small">ขนาด</label><select id="exportScale" class="control"><option value="0.5">0.5×</option><option value="1" selected>1× Original</option><option value="2">2×</option><option value="4">4×</option></select></div></div><div class="field"><label>คุณภาพ JPG/WebP <span id="qualityVal">92%</span></label><input id="quality" type="range" min="10" max="100" value="92"></div><div id="exportInfo" class="small">กรุณาเลือกรูปภาพ</div><button id="export" class="btn primary" disabled style="width:100%;margin-top:10px">ดาวน์โหลดผลงาน</button><button id="reset" class="btn" style="width:100%;margin-top:8px">รีเซ็ต Workspace</button></div>
</section></main>
<div id="toast" class="toast hidden"></div>
<div id="settingsModal" class="hidden" style="position:fixed;inset:0;background:#0009;display:grid;place-items:center;padding:16px;z-index:30"><section class="panel" style="width:min(460px,100%)"><h2>ตั้งค่า Storage</h2><p class="small">การเก็บ Model AI และ Cache ไว้ใน Profile ของ Neutron</p><label><input id="persist" type="checkbox"> ขอเก็บข้อมูลเว็บไซต์แบบถาวร (Persistent Storage)</label><p id="storageUsage" class="small">กำลังคำนวณ...</p><div class="row"><button id="clearData" class="btn danger">ล้าง Cache / IndexedDB</button><button id="closeSettings" class="btn">ปิด</button></div></section></div>
<script>
const $=s=>document.querySelector(s),state={file:null,source:null,foregroundBlob:null,foreground:null,bgImage:null,bgMode:'transparent',compare:false,comparePosition:.5,job:0,busy:false};
// Build the element map from the actual DOM instead of maintaining a manual ID list.
// Missing IDs in the old list (reset, resetAdjust and fit) caused a TypeError during
// initialization, aborting all later EventListener bindings (sliders, modes, export, etc.).
const el = Object.create(null);
for (const node of document.querySelectorAll('[id]')) {
  if (node.id) el[node.id] = node;
}
const requiredElements = [
  'canvas','drop','file','fileInfo','remove','cancel','progress','status','empty',
  'workspaceStatus','dimensions','compare','compareRange','bgColor','ga','gb','angle',
  'fitMode','blur','bgFile','bgUpload','scale','ox','oy','bright','contrast','sat',
  'opacity','shadow','shadowOpacity','format','exportScale','quality','export','exportInfo',
  'reset','resetAdjust','fit','theme','settings','settingsModal','persist','storageUsage',
  'clearData','closeSettings','network','toast'
];
const missingElements = requiredElements.filter(id => !el[id]);
if (missingElements.length) {
  throw new Error('Background Remover HTML is missing required elements: ' + missingElements.join(', '));
}
let engine=null,toastTimer=0;
function toast(s,error=false){const t=$('#toast');t.textContent=s;t.style.background=error?'#b91c1c':'#111827';t.classList.remove('hidden');clearTimeout(toastTimer);toastTimer=setTimeout(()=>t.classList.add('hidden'),3200)}
function status(s){el.status.textContent=s}function progress(p){el.progress.value=Math.max(0,Math.min(100,Number(p)||0))}
function bytes(n){const u=['B','KB','MB','GB'];let i=0;while(n>=1024&&i<3){n/=1024;i++}return `${n.toFixed(i?1:0)} ${u[i]}`}
function loadImage(blob){return new Promise((resolve,reject)=>{const u=URL.createObjectURL(blob),im=new Image();im.onload=()=>{URL.revokeObjectURL(u);resolve(im)};im.onerror=()=>{URL.revokeObjectURL(u);reject(Error('อ่านไฟล์รูปภาพไม่ได้'))};im.src=u})}
function validate(f){if(!f||!/^image\/(jpeg|png|webp|bmp)$/.test(f.type))throw Error('รองรับ JPG, PNG, WebP และ BMP');if(f.size>50*1024*1024)throw Error('ไฟล์ต้องไม่เกิน 50 MB')}
async function openFile(f){try{validate(f);state.job++;state.file=f;state.source=await loadImage(f);state.foregroundBlob=null;state.foreground=null;state.compare=false;el.canvas.classList.remove('hidden');el.empty.classList.add('hidden');el.fileInfo.classList.remove('hidden');el.fileInfo.textContent=`${f.name} · ${state.source.naturalWidth} × ${state.source.naturalHeight} px · ${bytes(f.size)}`;el.remove.disabled=false;el.export.disabled=false;el.compare.disabled=true;el.workspaceStatus.textContent='แสดงภาพต้นฉบับ';el.dimensions.textContent=`${state.source.naturalWidth} × ${state.source.naturalHeight} px`;resetAdjust();render();toast('โหลดรูปภาพเรียบร้อย')}catch(e){toast(e.message,true)}}
async function getEngine(){if(engine)return engine;const sources=['https://esm.sh/@imgly/background-removal?bundle','https://cdn.jsdelivr.net/npm/@imgly/background-removal/+esm'];let last;for(const src of sources){try{const m=await import(src);engine=m.default||m.removeBackground;if(typeof engine!=='function')throw Error('ไม่พบ AI removeBackground');return engine}catch(e){last=e}}throw last||Error('โหลด AI Engine ไม่สำเร็จ')}
async function removeBG(){if(!state.file||state.busy)return;const job=++state.job;state.busy=true;el.remove.disabled=true;el.cancel.classList.remove('hidden');status('กำลังโหลด AI Engine...');progress(2);$('#network').textContent='Connecting';try{const fn=await getEngine();if(job!==state.job)return;const blob=await fn(state.file,{output:{format:'image/png',quality:1},progress:(key,current,total)=>{if(job!==state.job)return;const p=total>0?current/total:0;progress(5+p*88);status(`${key||'AI'} ${Math.round(p*100)}%`);$('#network').textContent=(total>0&&current<total)?'Online':'Model ready'}});if(job!==state.job)return;state.foregroundBlob=blob;state.foreground=await loadImage(blob);if(job!==state.job)return;el.compare.disabled=false;el.workspaceStatus.textContent='ลบพื้นหลังเรียบร้อย';progress(100);status('เสร็จเรียบร้อย');render();toast('AI ลบพื้นหลังเรียบร้อย')}catch(e){if(job===state.job){console.error(e);status('ผิดพลาด: '+e.message);toast('ลบพื้นหลังไม่สำเร็จ: '+e.message,true)}}finally{if(job===state.job){state.busy=false;el.remove.disabled=false;el.cancel.classList.add('hidden');$('#network').textContent='Ready'}}}
function cancel(){if(!state.busy)return;state.job++;state.busy=false;el.remove.disabled=false;el.cancel.classList.add('hidden');status('ยกเลิกแล้ว');progress(0)}
function resetAdjust(){for(const [id,v] of Object.entries({scale:100,ox:0,oy:0,bright:100,contrast:100,sat:100,opacity:100,shadow:0,shadowOpacity:35}))$('#'+id).value=v;labels();render()}
function labels(){for(const [id,target,suffix] of [['scale','scaleVal','%'],['ox','xVal','%'],['oy','yVal','%'],['bright','brightVal','%'],['contrast','contrastVal','%'],['sat','satVal','%'],['opacity','opacityVal','%'],['shadow','shadowVal',' px'],['shadowOpacity','shadowOpacityVal','%'],['angle','angleVal','°'],['blur','blurVal',' px'],['quality','qualityVal','%']])$('#'+target).textContent=$('#'+id).value+suffix;updateExportInfo()}
function drawCover(ctx,img,w,h,fit){if(fit==='stretch'){ctx.drawImage(img,0,0,w,h);return}const ir=img.naturalWidth/img.naturalHeight,cr=w/h;let dw,dh;if((fit==='cover'&&ir>cr)||(fit==='contain'&&ir<cr)){dh=h;dw=h*ir}else{dw=w;dh=w/ir}ctx.drawImage(img,(w-dw)/2,(h-dh)/2,dw,dh)}
function draw(ctx,w,h,forceWhite=false){ctx.clearRect(0,0,w,h);if(forceWhite||state.bgMode==='color'){ctx.fillStyle=forceWhite?'#fff':el.bgColor.value;ctx.fillRect(0,0,w,h)}else if(state.bgMode==='gradient'){const a=Number(el.angle.value)*Math.PI/180,len=Math.abs(w*Math.cos(a))+Math.abs(h*Math.sin(a)),dx=Math.cos(a)*len/2,dy=Math.sin(a)*len/2,g=ctx.createLinearGradient(w/2-dx,h/2-dy,w/2+dx,h/2+dy);g.addColorStop(0,el.ga.value);g.addColorStop(1,el.gb.value);ctx.fillStyle=g;ctx.fillRect(0,0,w,h)}else if(state.bgMode==='image'&&state.bgImage){ctx.save();ctx.filter=`blur(${el.blur.value}px)`;const z=Number(el.blur.value)>0?1.08:1;ctx.translate(w/2,h/2);ctx.scale(z,z);ctx.translate(-w/2,-h/2);drawCover(ctx,state.bgImage,w,h,el.fitMode.value);ctx.restore()}
const im=state.foreground||state.source;if(!im)return;const base=Math.min(w/im.naturalWidth,h/im.naturalHeight),sc=Number(el.scale.value)/100,dw=im.naturalWidth*base*sc,dh=im.naturalHeight*base*sc,x=(w-dw)/2+Number(el.ox.value)/100*w/2,y=(h-dh)/2+Number(el.oy.value)/100*h/2;ctx.save();ctx.globalAlpha=Number(el.opacity.value)/100;ctx.filter=`brightness(${el.bright.value}%) contrast(${el.contrast.value}%) saturate(${el.sat.value}%)`;const sb=Number(el.shadow.value);if(sb>0){ctx.shadowColor=`rgba(0,0,0,${Number(el.shadowOpacity.value)/100})`;ctx.shadowBlur=sb;ctx.shadowOffsetY=Math.max(2,sb*.22)}ctx.drawImage(im,x,y,dw,dh);ctx.restore()}
function render(){if(!state.source)return;const maxW=1200,maxH=900,r=Math.min(1,maxW/state.source.naturalWidth,maxH/state.source.naturalHeight),w=Math.max(1,Math.round(state.source.naturalWidth*r)),h=Math.max(1,Math.round(state.source.naturalHeight*r));el.canvas.width=w;el.canvas.height=h;const c=el.canvas.getContext('2d');draw(c,w,h);if(state.compare&&state.source){const split=w*state.comparePosition;c.save();c.beginPath();c.rect(0,0,split,h);c.clip();c.clearRect(0,0,split,h);drawCover(c,state.source,w,h,'contain');c.restore();c.save();c.strokeStyle='#fff';c.lineWidth=2;c.beginPath();c.moveTo(split,0);c.lineTo(split,h);c.stroke();c.restore()}}
function updateExportInfo(){if(!state.source){el.exportInfo.textContent='กรุณาเลือกรูปภาพ';return}const s=Number(el.exportScale.value),w=Math.round(state.source.naturalWidth*s),h=Math.round(state.source.naturalHeight*s);el.exportInfo.textContent=`ขนาดส่งออก ${w.toLocaleString()} × ${h.toLocaleString()} px`}
function setMode(mode){state.bgMode=mode;document.querySelectorAll('.mode').forEach(b=>b.style.borderColor=b.dataset.mode===mode?'var(--primary)':'var(--border)');render()}
async function exportImage(){if(!state.source)return;const s=Number(el.exportScale.value),w=Math.round(state.source.naturalWidth*s),h=Math.round(state.source.naturalHeight*s);if(w*h>90000000){toast('ภาพใหญ่เกิน 90 ล้านพิกเซล กรุณาลดขนาดส่งออก',true);return}el.export.disabled=true;el.export.textContent='กำลังสร้างไฟล์...';try{const c=document.createElement('canvas');c.width=w;c.height=h;draw(c.getContext('2d'),w,h,el.format.value==='jpeg'&&state.bgMode==='transparent');const type=el.format.value==='jpeg'?'image/jpeg':el.format.value==='webp'?'image/webp':'image/png';const blob=await new Promise((ok,no)=>c.toBlob(b=>b?ok(b):no(Error('สร้างไฟล์ไม่สำเร็จ')),type,Number(el.quality.value)/100));const u=URL.createObjectURL(blob),a=document.createElement('a'),base=(state.file.name||'background').replace(/\.[^.]+$/,'').replace(/[^\w\u0E00-\u0E7F-]+/g,'-');a.href=u;a.download=base+'-removed.'+(type==='image/jpeg'?'jpg':type==='image/webp'?'webp':'png');document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),15000);toast('ส่งออกภาพเรียบร้อย')}catch(e){console.error(e);toast(e.message,true)}finally{el.export.disabled=false;el.export.textContent='ดาวน์โหลดผลงาน'}}
function resetAll(){cancel();state.file=null;state.source=null;state.foregroundBlob=null;state.foreground=null;state.bgImage=null;el.file.value='';el.bgFile.value='';el.canvas.classList.add('hidden');el.empty.classList.remove('hidden');el.fileInfo.classList.add('hidden');el.remove.disabled=true;el.export.disabled=true;el.compare.disabled=true;el.workspaceStatus.textContent='ยังไม่ได้เลือกรูปภาพ';progress(0);status('พร้อมใช้งาน');setMode('transparent');resetAdjust()}
function applyTheme(t){document.documentElement.dataset.theme=t;localStorage.setItem('neutron-bg-theme',t)}
$('#theme').value=localStorage.getItem('neutron-bg-theme')||'dark';applyTheme($('#theme').value);$('#theme').addEventListener('change',e=>applyTheme(e.target.value));
el.drop.onclick=()=>el.file.click();el.drop.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();el.file.click()}};el.file.onchange=e=>{if(e.target.files[0])openFile(e.target.files[0]);e.target.value=''};
['dragenter','dragover'].forEach(n=>el.drop.addEventListener(n,e=>{e.preventDefault();el.drop.classList.add('hot')}));['dragleave','drop'].forEach(n=>el.drop.addEventListener(n,e=>{e.preventDefault();el.drop.classList.remove('hot')}));el.drop.addEventListener('drop',e=>{const f=[...(e.dataTransfer.files||[])].find(x=>x.type.startsWith('image/'));if(f)openFile(f)});document.addEventListener('paste',e=>{const it=[...(e.clipboardData?.items||[])].find(x=>x.type.startsWith('image/'));if(it){const b=it.getAsFile();if(b)openFile(new File([b],'clipboard.png',{type:b.type||'image/png'}))}});
el.remove.onclick=removeBG;el.cancel.onclick=cancel;el.reset.onclick=resetAll;el.resetAdjust.onclick=resetAdjust;el.export.onclick=exportImage;el.compare.onclick=()=>{state.compare=!state.compare;el.compare.textContent=state.compare?'ปิด Before / After':'Before / After';render()};el.compareRange.oninput=()=>{state.comparePosition=Number(el.compareRange.value)/100;render()};el.fit.onclick=()=>el.canvas.scrollIntoView({behavior:'smooth',block:'center'});
document.querySelectorAll('.mode').forEach(b=>b.onclick=()=>{if(b.dataset.mode==='image'&&!state.bgImage){el.bgFile.click();return}setMode(b.dataset.mode)});el.bgUpload.onclick=()=>el.bgFile.click();el.bgFile.onchange=async e=>{const f=e.target.files[0];if(f){try{validate(f);state.bgImage=await loadImage(f);setMode('image')}catch(x){toast(x.message,true)}}e.target.value=''};
['bgColor','ga','gb','angle','fitMode','blur','scale','ox','oy','bright','contrast','sat','opacity','shadow','shadowOpacity','quality'].forEach(id=>$('#'+id).addEventListener('input',()=>{labels();render()}));el.exportScale.onchange=labels;
$('#settings').onclick=async()=>{$('#settingsModal').classList.remove('hidden');try{const p=await navigator.storage?.persisted?.();$('#persist').checked=!!p;const e=await navigator.storage?.estimate?.();$('#storageUsage').textContent=e?`พื้นที่ใช้งาน ${(e.usage/1048576).toFixed(2)} MB`:'ไม่รองรับการตรวจสอบ Storage'}catch(_){$('#storageUsage').textContent='ตรวจสอบไม่ได้'}};$('#closeSettings').onclick=()=>$('#settingsModal').classList.add('hidden');$('#persist').onchange=async e=>{if(e.target.checked){const ok=await navigator.storage?.persist?.();if(!ok){e.target.checked=false;toast('Browser ไม่อนุญาต Persistent Storage',true)}else toast('เปิด Persistent Storage แล้ว')}else{e.target.checked=true;toast('Browser ไม่รองรับการยกเลิก Persistent Storage โดยตรง',true)}};$('#clearData').onclick=async()=>{if(!confirm('ลบ Cache และ IndexedDB ของ Background Remover หรือไม่? Model อาจต้องดาวน์โหลดใหม่'))return;try{for(const k of await caches.keys())await caches.delete(k);if(indexedDB.databases){for(const d of await indexedDB.databases())if(d.name)indexedDB.deleteDatabase(d.name)}toast('ล้าง Cache/IndexedDB แล้ว');setTimeout(()=>location.reload(),800)}catch(e){toast('ล้าง Storage ไม่สำเร็จ: '+e.message,true)}};
document.addEventListener('keydown',e=>{const mod=e.ctrlKey||e.metaKey,tag=document.activeElement?.tagName;if(mod&&e.key.toLowerCase()==='o'){e.preventDefault();el.file.click()}if(mod&&e.key==='Enter'){e.preventDefault();removeBG()}if(mod&&e.key.toLowerCase()==='s'){e.preventDefault();exportImage()}if(!mod&&e.key.toLowerCase()==='r'&&!['INPUT','SELECT','TEXTAREA'].includes(tag))resetAdjust()});
labels();setMode('transparent');
</script></body></html>
'''

CALCULATOR_HTML = r'''<!doctype html>
<html lang="th"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Neutron Calculator</title>
<style>
:root{color-scheme:dark;--bg:#121722;--panel:#1c2534;--panel2:#273449;--text:#eef3fb;--muted:#9aa9bf;--accent:#6d8dff;--border:#35445d;--op:#34496a;--danger:#9c3946}
*{box-sizing:border-box}body{margin:0;min-height:100vh;background:radial-gradient(circle at 50% 0,#263b60,#121722 65%);color:var(--text);font:15px "Leelawadee UI","Segoe UI",sans-serif;display:grid;place-items:center;padding:22px}
.app{width:min(430px,100%);background:var(--panel);border:1px solid var(--border);border-radius:20px;padding:20px;box-shadow:0 24px 70px #0007}
.head{display:flex;align-items:center;justify-content:space-between;margin-bottom:16px}.head h1{margin:0;font-size:18px;letter-spacing:2px}.sub{color:var(--muted);font-size:11px}
.display{background:#0b111b;border:1px solid var(--border);border-radius:13px;padding:14px 16px;text-align:right;min-height:108px;display:flex;flex-direction:column;justify-content:flex-end;overflow:hidden;margin-bottom:12px}
#history{min-height:20px;color:var(--muted);font-size:13px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}#value{font-size:36px;font-weight:600;line-height:1.25;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-variant-numeric:tabular-nums}
.keys{display:grid;grid-template-columns:repeat(4,1fr);gap:8px}.keys button,.memory button{min-height:55px;border:1px solid var(--border);border-radius:11px;background:var(--panel2);color:var(--text);font:600 18px "Segoe UI",sans-serif;cursor:pointer;transition:.12s}.keys button:hover,.memory button:hover{filter:brightness(1.18);border-color:var(--accent)}.keys button:active,.memory button:active{transform:scale(.97)}.keys .utility{color:#b9c8ff;background:#263652}.keys .operator{background:var(--op)}.keys .clear{background:var(--danger);color:#fff}.keys .equals{background:var(--accent);color:#fff;border-color:transparent}.keys .zero{grid-column:span 2}.memory{display:grid;grid-template-columns:repeat(5,1fr);gap:7px;margin:10px 0}.memory button{min-height:34px;font-size:12px;background:#202d40;color:var(--muted)}.foot{margin-top:12px;color:var(--muted);font-size:11px;text-align:center}
</style></head><body><main class="app"><div class="head"><h1>NEUTRON CALCULATOR</h1><span class="sub">STANDARD</span></div>
<div class="display"><div id="history"></div><div id="value" aria-live="polite">0</div></div>
<div class="memory"><button data-action="mc">MC</button><button data-action="mr">MR</button><button data-action="mplus">M+</button><button data-action="mminus">M−</button><button data-action="ms">MS</button></div>
<div class="keys">
<button class="utility" data-action="percent">%</button><button class="utility" data-action="ce">CE</button><button class="clear" data-action="clear">C</button><button class="utility" data-action="back">⌫</button>
<button class="utility" data-action="sign">±</button><button class="utility" data-action="sqrt">√</button><button class="utility" data-action="square">x²</button><button class="operator" data-op="/">÷</button>
<button data-digit="7">7</button><button data-digit="8">8</button><button data-digit="9">9</button><button class="operator" data-op="*">×</button>
<button data-digit="4">4</button><button data-digit="5">5</button><button data-digit="6">6</button><button class="operator" data-op="-">−</button>
<button data-digit="1">1</button><button data-digit="2">2</button><button data-digit="3">3</button><button class="operator" data-op="+">+</button>
<button class="zero" data-digit="0">0</button><button data-action="decimal">.</button><button class="equals" data-action="equals">=</button>
</div><div class="foot">Keyboard: 0–9 · + − * / · Enter · Backspace · Esc</div></main>
<script>
(()=>{
 const $=id=>document.getElementById(id), value=$('value'), history=$('history');
 let current='0', accumulator=null, pending=null, replace=true, memory=0, lastOperand=null, lastOperator=null, error=false;
 const num=()=>Number(current);
 function format(n){if(!Number.isFinite(n))return 'Error';if(Object.is(n,-0))n=0;return Number(n.toPrecision(12)).toString()}
 function render(){value.textContent=current;}
 function setError(){current='Error';error=true;pending=null;accumulator=null;replace=true;history.textContent='';render()}
 function digit(d){if(error){current='0';error=false}if(replace){current=d;replace=false}else if(current.replace('-','').length<16)current=current==='0'?d:current+d;render()}
 function decimal(){if(error){current='0';error=false}if(replace){current='0.';replace=false}else if(!current.includes('.'))current+='.';render()}
 function calc(a,b,op){switch(op){case '+':return a+b;case '-':return a-b;case '*':return a*b;case '/':return b===0?NaN:a/b;default:return b}}
 function choose(op){if(error)return;const x=num();if(pending&& !replace){const r=calc(accumulator,x,pending);if(!Number.isFinite(r)){setError();return}current=format(r);accumulator=r;}else accumulator=x;pending=op;replace=true;lastOperator=null;history.textContent=format(accumulator)+' '+symbol(op);render()}
 const symbol=op=>({'/':'÷','*':'×','-':'−','+':'+'}[op]||op);
 function equals(){if(error)return;if(pending){const rhs=replace?accumulator:num(), lhs=accumulator, op=pending, r=calc(lhs,rhs,op);if(!Number.isFinite(r)){setError();return}history.textContent=format(lhs)+' '+symbol(op)+' '+format(rhs)+' =';current=format(r);accumulator=r;lastOperand=rhs;lastOperator=op;pending=null;replace=true;render()}else if(lastOperator){const r=calc(num(),lastOperand,lastOperator);if(!Number.isFinite(r)){setError();return}history.textContent=format(num())+' '+symbol(lastOperator)+' '+format(lastOperand)+' =';current=format(r);render();replace=true}}
 function clear(){current='0';accumulator=null;pending=null;replace=true;lastOperand=null;lastOperator=null;error=false;history.textContent='';render()}
 function act(a){if(a==='clear'){clear();return}if(a==='ce'){current='0';error=false;replace=true;render();return}if(a==='back'){if(error){clear();return}if(!replace)current=current.length<=1||current==='-0'?'0':current.slice(0,-1);render();return}if(error)return;
  if(a==='sign'){if(num()!==0)current=current.startsWith('-')?current.slice(1):'-'+current;render()}
  else if(a==='percent'){current=format(num()/100);replace=true;render()}
  else if(a==='sqrt'){const n=num();if(n<0){setError();return}history.textContent='√('+current+')';current=format(Math.sqrt(n));replace=true;render()}
  else if(a==='square'){const n=num();history.textContent='sqr('+current+')';current=format(n*n);replace=true;render()}
  else if(a==='decimal')decimal();else if(a==='equals')equals();
  else if(a==='mc')memory=0;else if(a==='mr'){current=format(memory);replace=true;render()}else if(a==='ms')memory=num();else if(a==='mplus')memory+=num();else if(a==='mminus')memory-=num();
 }
 document.querySelector('.keys').addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;if(b.dataset.digit!==undefined)digit(b.dataset.digit);else if(b.dataset.op)choose(b.dataset.op);else if(b.dataset.action)act(b.dataset.action)});
 document.querySelector('.memory').addEventListener('click',e=>{const b=e.target.closest('button');if(b)act(b.dataset.action)});
 document.addEventListener('keydown',e=>{if(/^[0-9]$/.test(e.key)){digit(e.key);e.preventDefault()}else if(e.key==='.'){decimal();e.preventDefault()}else if(['+','-','*','/'].includes(e.key)){choose(e.key);e.preventDefault()}else if(e.key==='Enter'||e.key==='='){equals();e.preventDefault()}else if(e.key==='Backspace'){act('back');e.preventDefault()}else if(e.key==='Escape'){clear();e.preventDefault()}else if(e.key==='%'){act('percent');e.preventDefault()}});
 render();
})();
</script></body></html>
'''

BASE64_DECODER_HTML = r'''<!doctype html><html lang="th"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Neutron Base64 Decoder</title>
<style>
:root{--p:#8b5cf6;--ph:#7c3aed;--bg:#0f172a;--panel:#1d2540;--text:#f8fafc;--muted:#a4aec2;--border:#ffffff20;--ok:#10b981;--input:#10182b}*{box-sizing:border-box}body{margin:0;min-height:100vh;padding:24px;background:linear-gradient(135deg,#0b1223,#1e1b4b);color:var(--text);font:14px "Leelawadee UI","Segoe UI",sans-serif;display:flex;justify-content:center;align-items:flex-start}.app{width:min(980px,100%);margin:18px auto;background:#ffffff08;border:1px solid var(--border);border-radius:22px;padding:clamp(18px,4vw,38px);box-shadow:0 20px 55px #0006;backdrop-filter:blur(16px)}header{text-align:center;margin-bottom:25px}h1{margin:0 0 8px;font-size:clamp(24px,4vw,34px);background:linear-gradient(90deg,#c084fc,#ec4899);color:transparent;background-clip:text}header p{color:var(--muted);margin:0}.tabs{display:flex;gap:8px;padding:6px;background:#0003;border:1px solid var(--border);border-radius:12px;margin-bottom:20px}.tab{flex:1;border:0;border-radius:8px;padding:12px;background:transparent;color:var(--muted);font-weight:700;cursor:pointer}.tab.active{background:var(--p);color:#fff}.pane{display:none}.pane.active{display:block}textarea{width:100%;min-height:150px;resize:vertical;background:var(--input);border:1px solid var(--border);border-radius:12px;padding:14px;color:var(--text);font:14px/1.6 Consolas,monospace;outline:none}textarea:focus{border-color:var(--p)}.drop{border:2px dashed var(--p);background:#8b5cf608;border-radius:15px;padding:38px 18px;text-align:center;cursor:pointer}.drop.hot{background:#8b5cf620;border-color:#c4b5fd}.drop b{font-size:18px}.muted{color:var(--muted)}.row{display:flex;gap:9px;justify-content:flex-end;flex-wrap:wrap;margin:12px 0}.btn{border:1px solid var(--border);border-radius:9px;padding:10px 16px;background:#ffffff0d;color:var(--text);cursor:pointer;font-weight:600}.btn.primary{background:var(--p);border-color:transparent}.btn:hover{filter:brightness(1.15)}.info{display:flex;gap:12px;align-items:center;padding:12px;border:1px solid var(--border);border-radius:10px;margin-top:14px;background:#ffffff08}.info strong{overflow-wrap:anywhere}.output{display:none;margin-top:24px}.outhead{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;margin-bottom:10px}.preview{min-height:150px;padding:16px;border:1px solid var(--border);border-radius:12px;background:#0003;display:grid;place-items:center}.preview img,.preview video{max-width:100%;max-height:430px;border-radius:8px}.preview audio{width:100%}.preview iframe{width:100%;height:440px;border:0}.preview textarea{width:100%;min-height:180px}.notice{color:var(--muted);font-size:12px;margin-top:10px}.toast{position:fixed;bottom:20px;left:50%;transform:translate(-50%,20px);opacity:0;background:var(--ok);color:white;padding:10px 18px;border-radius:24px;transition:.2s;pointer-events:none}.toast.show{opacity:1;transform:translate(-50%,0)}input[type=file]{display:none}
</style></head><body><main class="app"><header><h1>BASE64 DECODER</h1><p>ถอดรหัส Base64 กลับเป็นข้อความหรือไฟล์ พร้อม Preview ผลลัพธ์</p></header>
<div class="tabs"><button class="tab active" data-tab="textPane">ถอดรหัสจากข้อความ</button><button class="tab" data-tab="filePane">ถอดรหัสจากไฟล์ .txt</button></div>
<section id="textPane" class="pane active"><textarea id="textInput" placeholder="วาง Base64 หรือ Data URL เช่น data:image/png;base64,..."></textarea><div class="row"><button id="decodeText" class="btn primary">ถอดรหัสข้อมูล</button></div></section>
<section id="filePane" class="pane"><div id="drop" class="drop" tabindex="0"><b>ลากไฟล์ .txt มาวางที่นี่</b><p class="muted">หรือคลิกเพื่อเลือกไฟล์ข้อความที่เก็บ Base64</p></div><input id="fileInput" type="file" accept=".txt,text/plain"><div id="fileInfo" class="info" hidden><div>📄</div><div><strong id="fileName"></strong><div id="fileSize" class="muted"></div></div></div></section>
<section id="output" class="output"><div class="outhead"><strong id="outTitle">ผลลัพธ์การถอดรหัส</strong><div class="row" style="margin:0"><button id="copy" class="btn">คัดลอกข้อความ</button><button id="openLink" class="btn" hidden>เปิดลิงก์</button><button id="download" class="btn primary">ดาวน์โหลดไฟล์</button></div></div><div id="preview" class="preview"></div><div id="meta" class="notice"></div></section>
<p class="notice">ประมวลผลภายใน Browser ไม่ส่ง Base64 ไปยัง Server · รองรับ Data URL, Base64 URL-safe และไฟล์ข้อความขนาดไม่เกิน 100 MB</p></main><div id="toast" class="toast">ดำเนินการสำเร็จ</div>
<script>
(()=>{
 const $=id=>document.getElementById(id);let blob=null,mime='application/octet-stream',ext='bin',decodedText=null,objectUrl=null;
 const toast=t=>{const e=$('toast');e.textContent=t;e.classList.add('show');setTimeout(()=>e.classList.remove('show'),2200)};
 const fmt=n=>{if(!Number.isFinite(n))return '-';const u=['B','KB','MB','GB'];let i=0;while(n>=1024&&i<u.length-1){n/=1024;i++}return n.toFixed(i?2:0)+' '+u[i]};
 function clearOutput(){if(objectUrl){URL.revokeObjectURL(objectUrl);objectUrl=null}blob=null;decodedText=null;$('preview').replaceChildren();$('output').style.display='none';$('openLink').hidden=true;$('copy').hidden=true}
 function normalize(raw){let input=raw.trim(),data=input,declared='';const m=input.match(/^data:([^,]*?);base64,([\s\S]*)$/i);if(m){declared=(m[1].split(';')[0]||'').toLowerCase();data=m[2]}
 data=data.replace(/^\uFEFF/,'').replace(/[\s\u200B-\u200D\uFEFF]/g,'').replace(/-/g,'+').replace(/_/g,'/');if(!data)throw Error('ไม่พบข้อมูล Base64');if(!/^[A-Za-z0-9+/]*={0,2}$/.test(data))throw Error('พบอักขระที่ไม่ใช่ Base64');if(data.length%4===1)throw Error('ความยาว Base64 ไม่ถูกต้อง');data+= '='.repeat((4-data.length%4)%4);return {data,declared}}
 function sniff(b){const a=b.subarray(0,16),ascii=(s)=>String.fromCharCode(...a.slice(0,s.length))===s;
 if(a[0]===0x89&&ascii('\x89PNG\r\n\x1a\n'))return 'image/png';if(a[0]===0xff&&a[1]===0xd8)return 'image/jpeg';if(ascii('GIF8'))return 'image/gif';if(ascii('RIFF')&&String.fromCharCode(...b.subarray(8,12))==='WEBP')return 'image/webp';if(ascii('%PDF-'))return 'application/pdf';if(ascii('PK\x03\x04'))return 'application/zip';if(ascii('ID3'))return 'audio/mpeg';if(String.fromCharCode(...b.subarray(4,8))==='ftyp')return 'video/mp4';if(ascii('OggS'))return 'audio/ogg';if(ascii('RIFF')&&String.fromCharCode(...b.subarray(8,12))==='WAVE')return 'audio/wav';if(a[0]===0x1a&&a[1]===0x45&&a[2]===0xdf&&a[3]===0xa3)return 'video/webm';return ''}
 function guessExtension(t){return ({'image/jpeg':'jpg','image/png':'png','image/gif':'gif','image/webp':'webp','image/bmp':'bmp','application/pdf':'pdf','application/zip':'zip','audio/mpeg':'mp3','audio/ogg':'ogg','audio/wav':'wav','video/mp4':'mp4','video/webm':'webm','text/plain':'txt','text/html':'html','application/json':'json','application/octet-stream':'bin'})[t]||((t.split('/')[1]||'bin').split(';')[0].replace(/[^a-z0-9.+-]/gi,'')||'bin')}
 function utf8(bytes){try{const s=new TextDecoder('utf-8',{fatal:true}).decode(bytes);if(s.includes('\u0000'))return null;return s}catch(_){return null}}
 function render(){const p=$('preview');p.replaceChildren();objectUrl=URL.createObjectURL(blob);let el;
 if(mime.startsWith('image/')){el=document.createElement('img');el.src=objectUrl;el.alt='Decoded image'}
 else if(mime.startsWith('video/')){el=document.createElement('video');el.src=objectUrl;el.controls=true;el.playsInline=true}
 else if(mime.startsWith('audio/')){el=document.createElement('audio');el.src=objectUrl;el.controls=true}
 else if(mime==='application/pdf'){el=document.createElement('iframe');el.src=objectUrl;el.title='PDF preview'}
 else if(decodedText!==null){el=document.createElement('textarea');el.readOnly=true;el.value=decodedText;el.style.minHeight='200px';$('copy').hidden=false; if(/^https?:\/\//i.test(decodedText.trim()))$('openLink').hidden=false}
 else {el=document.createElement('p');el.className='muted';el.textContent='ไม่สามารถ Preview ไฟล์ชนิดนี้ได้ กรุณาดาวน์โหลดไฟล์เพื่อเปิดด้วยโปรแกรมที่เหมาะสม'}
 p.appendChild(el);$('output').style.display='block';$('meta').textContent=`MIME: ${mime} · ขนาด: ${fmt(blob.size)} · .${ext}`;$('outTitle').textContent='ผลลัพธ์การถอดรหัส'}
 function decode(raw){clearOutput();try{const {data,declared}=normalize(raw);const bin=atob(data),bytes=new Uint8Array(bin.length);for(let i=0;i<bin.length;i++)bytes[i]=bin.charCodeAt(i);const detected=sniff(bytes);mime=declared&&declared!=='application/octet-stream'?declared:(detected||'');if(!mime){decodedText=utf8(bytes);mime=decodedText!==null?'text/plain':'application/octet-stream'}else if(mime.startsWith('text/')||mime==='application/json'||mime.includes('xml'))decodedText=utf8(bytes);
 if(!mime)mime='application/octet-stream';if(!mime.startsWith('text/')&&mime!=='application/json'&&!mime.includes('xml')&&detected&&(!declared||declared==='application/octet-stream'))mime=detected;ext=guessExtension(mime);blob=new Blob([bytes],{type:mime});render();toast('ถอดรหัสสำเร็จ')}catch(e){clearOutput();alert('ถอดรหัสไม่สำเร็จ: '+e.message)}}
 function switchTab(id){document.querySelectorAll('.tab').forEach(b=>b.classList.toggle('active',b.dataset.tab===id));document.querySelectorAll('.pane').forEach(p=>p.classList.toggle('active',p.id===id));clearOutput()}
 document.querySelectorAll('.tab').forEach(b=>b.addEventListener('click',()=>switchTab(b.dataset.tab)));
 $('decodeText').addEventListener('click',()=>{if(!$('textInput').value.trim()){alert('กรุณาวาง Base64 ก่อน');return}decode($('textInput').value)});
 async function processFile(f){if(!f)return;if(f.size>100*1024*1024){alert('ไฟล์ข้อความใหญ่เกิน 100 MB');return}if(!/\.txt$/i.test(f.name)&&f.type!=='text/plain'){alert('รองรับไฟล์ข้อความ .txt เท่านั้น');return}$('fileName').textContent=f.name;$('fileSize').textContent=fmt(f.size);$('fileInfo').hidden=false;try{decode(await f.text())}catch(e){alert('อ่านไฟล์ไม่สำเร็จ: '+e.message)}}
 $('fileInput').addEventListener('change',e=>{processFile(e.target.files[0]);e.target.value=''});const drop=$('drop');drop.addEventListener('click',()=>$('fileInput').click());drop.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();$('fileInput').click()}});
 ['dragenter','dragover'].forEach(n=>drop.addEventListener(n,e=>{e.preventDefault();drop.classList.add('hot')}));['dragleave','drop'].forEach(n=>drop.addEventListener(n,e=>{e.preventDefault();drop.classList.remove('hot')}));drop.addEventListener('drop',e=>processFile(e.dataTransfer.files[0]));
 $('copy').addEventListener('click',async()=>{if(decodedText===null)return;try{await navigator.clipboard.writeText(decodedText);toast('คัดลอกข้อความแล้ว')}catch(_){const t=$('preview').querySelector('textarea');if(t){t.select();document.execCommand('copy');toast('คัดลอกข้อความแล้ว')}}});
 $('openLink').addEventListener('click',()=>{if(decodedText&&/^https?:\/\//i.test(decodedText.trim()))window.open(decodedText.trim(),'_blank','noopener,noreferrer')});
 $('download').addEventListener('click',()=>{if(!blob)return;const u=URL.createObjectURL(blob),a=document.createElement('a');a.href=u;a.download='decoded_file.'+ext;document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),30000)});
 window.addEventListener('beforeunload',()=>{if(objectUrl)URL.revokeObjectURL(objectUrl)});
})();
</script></body></html>
'''

BASE64_ENCODER_HTML = r'''<!doctype html><html lang="th"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Neutron Base64 Encoder</title>
<style>
:root{--p:#4f46e5;--ph:#4338ca;--text:#f8fafc;--muted:#a4aec2;--border:#ffffff20;--input:#10182b;--ok:#10b981}*{box-sizing:border-box}body{margin:0;min-height:100vh;padding:24px;background:linear-gradient(135deg,#0f172a,#1e1b4b);color:var(--text);font:14px "Leelawadee UI","Segoe UI",sans-serif;display:flex;justify-content:center;align-items:flex-start}.app{width:min(980px,100%);margin:18px auto;background:#ffffff08;border:1px solid var(--border);border-radius:22px;padding:clamp(18px,4vw,38px);box-shadow:0 20px 55px #0006;backdrop-filter:blur(16px)}header{text-align:center;margin-bottom:25px}h1{margin:0 0 8px;font-size:clamp(24px,4vw,34px);background:linear-gradient(90deg,#818cf8,#c084fc);color:transparent;background-clip:text}header p{color:var(--muted);margin:0}.tabs{display:flex;gap:8px;padding:6px;background:#0003;border:1px solid var(--border);border-radius:12px;margin-bottom:20px}.tab{flex:1;border:0;border-radius:8px;padding:12px;background:transparent;color:var(--muted);font-weight:700;cursor:pointer}.tab.active{background:var(--p);color:#fff}.pane{display:none}.pane.active{display:block}textarea{width:100%;min-height:150px;resize:vertical;background:var(--input);border:1px solid var(--border);border-radius:12px;padding:14px;color:var(--text);font:14px/1.6 Consolas,monospace;outline:none}textarea:focus{border-color:var(--p)}.drop{border:2px dashed var(--p);background:#4f46e508;border-radius:15px;padding:38px 18px;text-align:center;cursor:pointer}.drop.hot{background:#4f46e520;border-color:#a5b4fc}.drop b{font-size:18px}.muted{color:var(--muted)}.row{display:flex;gap:9px;justify-content:flex-end;flex-wrap:wrap;margin:12px 0}.btn{border:1px solid var(--border);border-radius:9px;padding:10px 16px;background:#ffffff0d;color:var(--text);cursor:pointer;font-weight:600}.btn.primary{background:var(--p);border-color:transparent}.btn:hover{filter:brightness(1.15)}.info{display:flex;gap:12px;align-items:center;padding:12px;border:1px solid var(--border);border-radius:10px;margin-top:14px;background:#ffffff08}.info strong{overflow-wrap:anywhere}.output{display:none;margin-top:24px}.outhead{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;margin-bottom:10px}.notice{color:var(--muted);font-size:12px;margin-top:10px}input[type=file]{display:none}.count{font-size:12px;color:var(--muted);margin:0 auto 0 0}.toast{position:fixed;bottom:20px;left:50%;transform:translate(-50%,20px);opacity:0;background:var(--ok);color:white;padding:10px 18px;border-radius:24px;transition:.2s;pointer-events:none}.toast.show{opacity:1;transform:translate(-50%,0)}
</style></head><body><main class="app"><header><h1>BASE64 ENCODER</h1><p>แปลงไฟล์ทุกประเภทหรือข้อความ UTF-8 เป็น Base64</p></header>
<div class="tabs"><button class="tab active" data-tab="filePane">แปลงจากไฟล์</button><button class="tab" data-tab="textPane">แปลงจากข้อความ</button></div>
<section id="filePane" class="pane active"><div id="drop" class="drop" tabindex="0"><b>ลากไฟล์มาวางที่นี่</b><p class="muted">หรือคลิกเพื่อเลือกไฟล์ · รองรับทุกนามสกุล</p><p class="muted">ผลลัพธ์เป็น Data URL (data:[MIME];base64,...) เพื่อรักษาชนิดไฟล์</p></div><input id="fileInput" type="file"><div id="fileInfo" class="info" hidden><div>📄</div><div><strong id="fileName"></strong><div id="fileSize" class="muted"></div></div></div></section>
<section id="textPane" class="pane"><textarea id="textInput" placeholder="พิมพ์หรือวางข้อความ UTF-8 ที่ต้องการเข้ารหัส"></textarea><div class="row"><button id="encodeText" class="btn primary">แปลงข้อความ</button></div></section>
<section id="output" class="output"><div class="outhead"><strong>ผลลัพธ์ Base64</strong><span id="count" class="count">0 ตัวอักษร</span><div class="row" style="margin:0"><button id="copy" class="btn">คัดลอก</button><button id="download" class="btn primary">ดาวน์โหลด (.txt)</button></div></div><textarea id="result" readonly spellcheck="false"></textarea></section><p class="notice">ประมวลผลภายใน Browser · รองรับไฟล์สูงสุด 100 MB · ภาษาไทยและ Unicode ใช้ UTF-8</p></main><div id="toast" class="toast">ดำเนินการสำเร็จ</div>
<script>
(()=>{
 const $=id=>document.getElementById(id);let result='';const toast=t=>{const e=$('toast');e.textContent=t;e.classList.add('show');setTimeout(()=>e.classList.remove('show'),2200)};const fmt=n=>{const u=['B','KB','MB','GB'];let i=0;while(n>=1024&&i<u.length-1){n/=1024;i++}return n.toFixed(i?2:0)+' '+u[i]};
 function bytesToBase64(bytes){let bin='',chunk=0x8000;for(let i=0;i<bytes.length;i+=chunk)bin+=String.fromCharCode(...bytes.subarray(i,Math.min(i+chunk,bytes.length)));return btoa(bin)}
 function show(text){result=text;$('result').value=text;$('count').textContent=text.length.toLocaleString('en-US')+' ตัวอักษร';$('output').style.display='block';$('output').scrollIntoView({behavior:'smooth',block:'nearest'})}
 function switchTab(id){document.querySelectorAll('.tab').forEach(b=>b.classList.toggle('active',b.dataset.tab===id));document.querySelectorAll('.pane').forEach(p=>p.classList.toggle('active',p.id===id));$('output').style.display='none';$('result').value='';result=''}
 document.querySelectorAll('.tab').forEach(b=>b.addEventListener('click',()=>switchTab(b.dataset.tab)));
 $('encodeText').addEventListener('click',()=>{const t=$('textInput').value;if(!t.length){alert('กรุณากรอกข้อความก่อน');return}try{show(bytesToBase64(new TextEncoder().encode(t)));toast('เข้ารหัสข้อความสำเร็จ')}catch(e){alert('เข้ารหัสไม่สำเร็จ: '+e.message)}});
 async function processFile(f){if(!f)return;if(f.size>100*1024*1024){alert('ไฟล์ใหญ่เกิน 100 MB');return}$('fileName').textContent=f.name;$('fileSize').textContent=fmt(f.size)+' · '+(f.type||'application/octet-stream');$('fileInfo').hidden=false;try{const data=await new Promise((resolve,reject)=>{const r=new FileReader();r.onload=()=>resolve(String(r.result));r.onerror=()=>reject(r.error||Error('อ่านไฟล์ไม่สำเร็จ'));r.readAsDataURL(f)});show(data);toast('แปลงไฟล์สำเร็จ')}catch(e){alert('แปลงไฟล์ไม่สำเร็จ: '+e.message)}}
 $('fileInput').addEventListener('change',e=>{processFile(e.target.files[0]);e.target.value=''});const drop=$('drop');drop.addEventListener('click',()=>$('fileInput').click());drop.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();$('fileInput').click()}});['dragenter','dragover'].forEach(n=>drop.addEventListener(n,e=>{e.preventDefault();drop.classList.add('hot')}));['dragleave','drop'].forEach(n=>drop.addEventListener(n,e=>{e.preventDefault();drop.classList.remove('hot')}));drop.addEventListener('drop',e=>processFile(e.dataTransfer.files[0]));
 $('copy').addEventListener('click',async()=>{try{await navigator.clipboard.writeText(result);toast('คัดลอกแล้ว')}catch(_){$('result').select();document.execCommand('copy');toast('คัดลอกแล้ว')}});
 $('download').addEventListener('click',()=>{if(!result)return;const blob=new Blob([result],{type:'text/plain;charset=utf-8'}),u=URL.createObjectURL(blob),a=document.createElement('a');a.href=u;a.download='base64_encoded_output.txt';document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),30000)});
})();
</script></body></html>
'''

MEDIA_DIAGNOSTICS_HTML = r'''<!doctype html><html lang="th"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Neutron Video Diagnostics</title>
<style>
:root{--bg:#111827;--panel:#1f2937;--panel2:#263449;--text:#f9fafb;--muted:#9ca3af;--border:#374151;--ok:#16a34a;--warn:#d97706;--bad:#dc2626;--accent:#6d8dff}*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--text);font:14px "Leelawadee UI","Segoe UI",sans-serif;padding:24px}.wrap{max-width:1000px;margin:auto}.head{border-bottom:1px solid var(--border);padding-bottom:14px;margin-bottom:16px}h1{margin:0 0 5px;font-size:24px;letter-spacing:2px}.muted{color:var(--muted)}.card{background:var(--panel);border:1px solid var(--border);border-radius:13px;padding:15px;margin:12px 0}.row{display:flex;gap:10px;flex-wrap:wrap;align-items:center}.btn{background:var(--panel2);border:1px solid var(--border);border-radius:8px;color:var(--text);padding:9px 14px;cursor:pointer}.btn.primary{background:var(--accent);border:0}.table{width:100%;border-collapse:collapse;margin-top:9px}.table th,.table td{text-align:left;border-bottom:1px solid var(--border);padding:9px 8px;vertical-align:top}.table th{color:var(--muted);font-weight:600}.yes{color:#4ade80}.no{color:#f87171}.maybe{color:#fbbf24}pre{white-space:pre-wrap;word-break:break-word;color:var(--muted);font:12px/1.6 Consolas,monospace}.note{line-height:1.65;color:var(--muted)}.status{font-weight:700}
</style></head><body><main class="wrap"><header class="head"><h1>NEUTRON VIDEO DIAGNOSTICS</h1><div class="muted">ตรวจความสามารถจริงจาก Chromium / QtWebEngine ที่กำลังรันอยู่</div></header>
<section class="card"><div class="row"><strong>ผลการตรวจสอบ Media Codecs</strong><button id="run" class="btn primary">ตรวจใหม่</button><button id="copy" class="btn">Copy Report</button></div><div id="summary" class="note">กำลังตรวจสอบ…</div><table class="table"><thead><tr><th>Codec / Feature</th><th>HTMLVideoElement</th><th>MSE</th><th>MediaCapabilities</th></tr></thead><tbody id="rows"></tbody></table></section>
<section class="card"><strong>Browser Runtime</strong><pre id="runtime">กำลังตรวจสอบ…</pre></section>
<section class="card"><strong>ข้อจำกัดสำคัญของ Qt WebEngine</strong><p class="note">H.264 / AAC ใน MP4 ต้องมี Proprietary Codec เปิดอยู่ใน Qt WebEngine ตอน Build (`-webengine-proprietary-codecs`) หากผลด้านบนเป็น Not supported จะไม่สามารถเพิ่ม Decoder ด้วย Python หรือ PyInstaller flags ได้ ต้องใช้ QtWebEngine Binary ที่ Build พร้อม codec ดังกล่าว และตรวจสอบเงื่อนไข License ก่อนแจกจ่าย</p><p class="note">Chromium 140 ยังไม่มี Native HLS Playback ในรุ่นนี้ หากมี MSE และ H.264/AAC ที่รองรับ สามารถใช้เว็บเพลเยอร์ที่มี hls.js เพื่อเล่น HLS ได้ ส่วน MediaCapabilities จะรายงานตาม Decoder ที่ติดตั้งจริง</p><p class="note">Widevine / DRM เป็นอีกส่วนหนึ่งต่างหาก การมี H.264 ไม่ได้แปลว่าจะเล่นบริการ DRM ได้โดยอัตโนมัติ</p></section></main>
<script>
(()=>{
 const $=id=>document.getElementById(id),video=document.createElement('video');
 const tests=[
  ['H.264 (MP4)','video/mp4; codecs="avc1.42E01E"','video/mp4; codecs="avc1.42E01E"'],
  ['H.265 / HEVC','video/mp4; codecs="hvc1.1.6.L93.B0"','video/mp4; codecs="hvc1.1.6.L93.B0"'],
  ['AAC','audio/mp4; codecs="mp4a.40.2"','audio/mp4; codecs="mp4a.40.2"'],
  ['VP8','video/webm; codecs="vp8"','video/webm; codecs="vp8"'],
  ['VP9','video/webm; codecs="vp9"','video/webm; codecs="vp9"'],
  ['AV1','video/mp4; codecs="av01.0.05M.08"','video/mp4; codecs="av01.0.05M.08"'],
  ['Opus','audio/webm; codecs="opus"','audio/webm; codecs="opus"']
 ];
 const cls=v=>v==='no'||v==='not supported'?'no':v==='yes'||v==='probably'||v==='maybe'||String(v).startsWith('supported')?'yes':'maybe';
 async function run(){const rows=[],report={userAgent:navigator.userAgent,platform:navigator.platform,language:navigator.language,secureContext:isSecureContext,mediaSource:!!window.MediaSource,hlsNative:video.canPlayType('application/vnd.apple.mpegurl'),hlsAlternate:video.canPlayType('application/x-mpegURL'),mse:{h264:!!window.MediaSource&&MediaSource.isTypeSupported('video/mp4; codecs="avc1.42E01E"'),aac:!!window.MediaSource&&MediaSource.isTypeSupported('audio/mp4; codecs="mp4a.40.2"'),h264Aac:!!window.MediaSource&&MediaSource.isTypeSupported('video/mp4; codecs="avc1.42E01E, mp4a.40.2"'),webmVp9:!!window.MediaSource&&MediaSource.isTypeSupported('video/webm; codecs="vp9"')},codecs:{}};
  for(const [name,mime,mseMime] of tests){const playable=video.canPlayType(mime)||'not supported',mse=!!window.MediaSource&&MediaSource.isTypeSupported(mseMime);let capability='not tested',capabilityDetails=null;if(navigator.mediaCapabilities?.decodingInfo){try{const isAudio=name==='AAC'||name==='Opus';const cfg=isAudio?{type:'file',audio:{contentType:mime,channels:'2',bitrate:128000,samplerate:48000}}:{type:'file',video:{contentType:mime,width:1920,height:1080,bitrate:5000000,framerate:30}};const d=await navigator.mediaCapabilities.decodingInfo(cfg);capabilityDetails={supported:!!d.supported,smooth:!!d.smooth,powerEfficient:!!d.powerEfficient};capability=`${d.supported?'supported':'not supported'} / ${d.smooth?'smooth':'not smooth'} / ${d.powerEfficient?'power-efficient':'not power-efficient'}`}catch(e){capability='not supported'}}report.codecs[name]={mime,canPlayType:playable,mse,mediaCapabilities:capability,mediaCapabilitiesDetails:capabilityDetails};rows.push(`<tr><td>${name}</td><td class="${cls(playable==='not supported'?'no':playable)}">${playable}</td><td class="${mse?'yes':'no'}">${mse?'yes':'no'}</td><td class="${cls(capability)}">${capability}</td></tr>`)}
  const hls=report.hlsNative||report.hlsAlternate||'not supported';report.hlsNative=hls;report.mseSupported=!!window.MediaSource;let key='not available';if(navigator.requestMediaKeySystemAccess){try{await navigator.requestMediaKeySystemAccess('com.widevine.alpha',[{initDataTypes:['cenc'],videoCapabilities:[{contentType:'video/mp4; codecs="avc1.42E01E"'}],audioCapabilities:[{contentType:'audio/mp4; codecs="mp4a.40.2"'}]}]);key='Widevine key system available'}catch(_){key='Widevine not available'}}report.keySystem=key;
  rows.push(`<tr><td>H.264 + AAC (MSE combined)</td><td class="muted">—</td><td class="${report.mse.h264Aac?'yes':'no'}">${report.mse.h264Aac?'yes':'no'}</td><td class="muted">—</td></tr>`);$('rows').innerHTML=rows.join('');$('runtime').textContent=JSON.stringify(report,null,2);$('summary').textContent=`MSE: ${report.mseSupported?'Available':'Unavailable'} · Native HLS: ${hls} · DRM: ${key}`;window.__neutronMediaReport=report;
 }
 $('run').addEventListener('click',run);$('copy').addEventListener('click',async()=>{try{await navigator.clipboard.writeText(JSON.stringify(window.__neutronMediaReport||{},null,2));$('summary').textContent='คัดลอกรายงานแล้ว'}catch(e){$('summary').textContent='คัดลอกไม่สำเร็จ: '+e.message}});run().catch(e=>{$('summary').textContent='Diagnostic failed: '+e.message});
})();
</script></body></html>
'''


MUSIC_PLAYER_HTML = '<!DOCTYPE html>\n<html lang="th" data-theme="light">\n<head>\n<meta charset="UTF-8">\n<meta name="viewport" content="width=device-width, initial-scale=1.0, viewport-fit=cover">\n<meta name="theme-color" content="#6366f1">\n<title>SonicStream — Web Music Player</title>\n<style>\n:root {\n    --bg-color: #f0f2f5;\n    --card-bg: #ffffff;\n    --text-main: #1a1a1a;\n    --text-dim: #666666;\n    --accent: #6366f1;\n    --accent-hover: #4f46e5;\n    --danger: #ef4444;\n    --shadow: 0 10px 25px -5px rgba(0, 0, 0, 0.1);\n}\n\n[data-theme="dark"] {\n    --bg-color: #0f172a;\n    --card-bg: #1e293b;\n    --text-main: #f8fafc;\n    --text-dim: #94a3b8;\n    --accent: #818cf8;\n    --accent-hover: #a5b4fc;\n}\n\n* { box-sizing: border-box; margin: 0; padding: 0; font-family: system-ui, sans-serif; }\nbody { background: var(--bg-color); color: var(--text-main); height: 100vh; display: flex; flex-direction: column; }\n.app-container { max-width: 1200px; margin: 0 auto; width: 100%; padding: 20px; display: flex; flex-direction: column; gap: 20px; height: 100%; }\n.card { background: var(--card-bg); border-radius: 16px; padding: 20px; box-shadow: var(--shadow); }\n.hidden { display: none !important; }\n.btn-danger { border: 1px solid var(--danger); color: var(--danger); padding: 8px 16px; border-radius: 8px; background: transparent; cursor: pointer; }\n.btn-danger:hover { background: var(--danger); color: white; }\n\n/* ---------- Base / Layout ---------- */\nhtml, body { overflow: hidden; }\nbody { transition: background .25s ease, color .25s ease; -webkit-tap-highlight-color: transparent; }\nbutton, input, label { font-size: 14px; }\n::selection { background: var(--accent); color: #fff; }\n\n.app-header {\n    display: flex; align-items: center; justify-content: space-between;\n    gap: 12px; flex-wrap: wrap; padding: 16px 20px;\n}\n.brand { display: flex; align-items: center; gap: 10px; font-size: 22px; font-weight: 800; letter-spacing: -.5px; }\n.brand .logo-dot {\n    width: 34px; height: 34px; border-radius: 10px; display: grid; place-items: center;\n    background: linear-gradient(135deg, var(--accent), #ec4899); color: #fff; font-size: 18px;\n    box-shadow: 0 6px 14px -4px var(--accent);\n}\n.brand small { display: block; font-size: 11px; font-weight: 500; color: var(--text-dim); letter-spacing: .4px; }\n.top-controls { display: flex; align-items: center; gap: 10px; flex-wrap: wrap; }\n\n.btn {\n    border: 0; border-radius: 10px; padding: 10px 16px; cursor: pointer;\n    font-weight: 600; display: inline-flex; align-items: center; gap: 8px;\n    transition: transform .12s ease, background .2s ease, color .2s ease, box-shadow .2s ease;\n    user-select: none; white-space: nowrap;\n}\n.btn:active { transform: scale(.96); }\n.btn-primary { background: var(--accent); color: #fff; box-shadow: 0 6px 16px -6px var(--accent); }\n.btn-primary:hover { background: var(--accent-hover); }\n.btn-ghost { background: transparent; color: var(--text-main); border: 1px solid rgba(128,128,128,.32); }\n.btn-ghost:hover { border-color: var(--accent); color: var(--accent); }\n.btn-soft { background: rgba(99,102,241,.12); color: var(--accent); }\n.btn-soft:hover { background: rgba(99,102,241,.22); }\n.btn-danger { font-weight: 600; transition: background .2s ease, color .2s ease, transform .12s ease; }\n.btn-danger:active { transform: scale(.96); }\n\n/* ---------- Main grid ---------- */\n.main-grid {\n    flex: 1; min-height: 0; display: grid; gap: 20px;\n    grid-template-columns: minmax(320px, 420px) 1fr;\n}\n\n/* ---------- Player card ---------- */\n.player-card { display: flex; flex-direction: column; gap: 18px; min-height: 0; overflow-y: auto; }\n.album-art {\n    width: 100%; aspect-ratio: 1 / 1; max-height: 260px; border-radius: 20px;\n    background: linear-gradient(135deg, var(--accent) 0%, #a855f7 50%, #ec4899 100%);\n    display: grid; place-items: center; position: relative; overflow: hidden;\n    box-shadow: 0 18px 40px -18px var(--accent); flex-shrink: 0;\n}\n.album-art::after {\n    content: ""; position: absolute; inset: -40%;\n    background: radial-gradient(circle at 30% 30%, rgba(255,255,255,.35), transparent 55%);\n}\n.album-art svg { width: 46%; height: 46%; position: relative; z-index: 2; filter: drop-shadow(0 6px 12px rgba(0,0,0,.25)); }\n.album-art.playing svg { animation: bob 2.4s ease-in-out infinite; }\n@keyframes bob { 0%,100% { transform: translateY(0) rotate(0deg); } 50% { transform: translateY(-8px) rotate(-4deg); } }\n\n.track-meta { text-align: center; }\n.track-meta h2 {\n    font-size: 20px; font-weight: 700; line-height: 1.35;\n    overflow: hidden; text-overflow: ellipsis; white-space: nowrap;\n}\n.track-meta p { color: var(--text-dim); font-size: 14px; margin-top: 4px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }\n\n.progress-container { display: flex; align-items: center; gap: 10px; }\n.progress-container span { font-size: 12px; color: var(--text-dim); font-variant-numeric: tabular-nums; min-width: 38px; text-align: center; }\n.progress-bar {\n    flex: 1; height: 8px; background: rgba(128,128,128,.25); border-radius: 99px;\n    cursor: pointer; position: relative; touch-action: none;\n}\n.progress-bar::before { content: ""; position: absolute; inset: -12px 0; }\n.progress-fill { height: 100%; width: 0%; background: var(--accent); border-radius: 99px; position: relative; }\n.progress-fill::after {\n    content: ""; position: absolute; right: -6px; top: 50%; transform: translateY(-50%);\n    width: 14px; height: 14px; border-radius: 50%; background: #fff; border: 3px solid var(--accent);\n    box-shadow: 0 2px 6px rgba(0,0,0,.25); opacity: 0; transition: opacity .18s ease;\n}\n.progress-bar:hover .progress-fill::after, .progress-bar.dragging .progress-fill::after { opacity: 1; }\n\n.controls { display: flex; align-items: center; justify-content: center; gap: 14px; }\n.ctrl-btn {\n    width: 48px; height: 48px; border-radius: 50%; border: 0; cursor: pointer;\n    background: rgba(128,128,128,.14); color: var(--text-main);\n    display: grid; place-items: center; font-size: 18px;\n    transition: transform .12s ease, background .2s ease, color .2s ease;\n}\n.ctrl-btn:hover { background: rgba(99,102,241,.2); color: var(--accent); }\n.ctrl-btn:active { transform: scale(.9); }\n.ctrl-btn.main {\n    width: 64px; height: 64px; font-size: 24px; background: var(--accent); color: #fff;\n    box-shadow: 0 10px 24px -8px var(--accent);\n}\n.ctrl-btn.main:hover { background: var(--accent-hover); color: #fff; }\n.ctrl-btn svg { width: 22px; height: 22px; fill: currentColor; pointer-events: none; }\n.ctrl-btn.main svg { width: 28px; height: 28px; }\n\n.mode-row { display: flex; align-items: center; justify-content: center; gap: 8px; flex-wrap: wrap; }\n.mode-btn {\n    border: 1px solid rgba(128,128,128,.3); background: transparent; color: var(--text-dim);\n    padding: 7px 13px; border-radius: 99px; cursor: pointer; font-size: 12.5px; font-weight: 600;\n    transition: all .18s ease;\n}\n.mode-btn:hover { color: var(--accent); border-color: var(--accent); }\n.mode-btn.active { background: var(--accent); border-color: var(--accent); color: #fff; }\n\n.volume-row { display: flex; align-items: center; gap: 10px; }\n.volume-row .vol-icon { font-size: 16px; cursor: pointer; user-select: none; }\ninput[type="range"] {\n    -webkit-appearance: none; appearance: none; flex: 1; height: 6px; border-radius: 99px;\n    background: rgba(128,128,128,.25); outline: none; cursor: pointer;\n}\ninput[type="range"]::-webkit-slider-thumb {\n    -webkit-appearance: none; width: 16px; height: 16px; border-radius: 50%;\n    background: var(--accent); border: 3px solid var(--card-bg); box-shadow: 0 1px 4px rgba(0,0,0,.3);\n}\ninput[type="range"]::-moz-range-thumb {\n    width: 14px; height: 14px; border: 3px solid var(--card-bg); border-radius: 50%; background: var(--accent);\n}\n\n/* ---------- Playlist card ---------- */\n.playlist-card { display: flex; flex-direction: column; min-height: 0; }\n.playlist-header {\n    display: flex; align-items: center; justify-content: space-between;\n    gap: 12px; flex-wrap: wrap; padding-bottom: 14px; border-bottom: 1px solid rgba(128,128,128,.18);\n}\n.playlist-header h3 { font-size: 17px; font-weight: 700; display: flex; align-items: center; gap: 8px; }\n.count-badge {\n    background: rgba(99,102,241,.15); color: var(--accent); font-size: 11.5px; font-weight: 700;\n    padding: 3px 9px; border-radius: 99px;\n}\n.playlist-actions { display: flex; gap: 8px; flex-wrap: wrap; margin-left: auto; }\n.playlist-actions .btn { padding: 8px 14px; font-size: 13px; }\n\n#playlist-items { list-style: none; overflow-y: auto; flex: 1; min-height: 0; margin-top: 8px; padding-right: 4px; }\n#playlist-items::-webkit-scrollbar { width: 8px; }\n#playlist-items::-webkit-scrollbar-thumb { background: rgba(128,128,128,.35); border-radius: 99px; }\n#playlist-items::-webkit-scrollbar-track { background: transparent; }\n\n.track-item {\n    display: flex; align-items: center; gap: 12px; padding: 10px 12px; border-radius: 12px;\n    cursor: pointer; transition: background .18s ease; margin-bottom: 4px;\n}\n.track-item:hover { background: rgba(128,128,128,.12); }\n.track-item.active { background: rgba(99,102,241,.15); }\n.track-item.active .t-title { color: var(--accent); font-weight: 700; }\n.track-item.missing { opacity: .55; }\n.t-index {\n    width: 26px; flex-shrink: 0; text-align: center; font-size: 12.5px;\n    color: var(--text-dim); font-variant-numeric: tabular-nums;\n}\n.t-info { flex: 1; min-width: 0; }\n.t-title { font-size: 14px; font-weight: 600; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }\n.t-sub { font-size: 12px; color: var(--text-dim); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; margin-top: 2px; }\n.t-dur { font-size: 12px; color: var(--text-dim); font-variant-numeric: tabular-nums; flex-shrink: 0; }\n.t-remove {\n    border: 0; background: transparent; color: var(--text-dim); cursor: pointer;\n    width: 26px; height: 26px; border-radius: 8px; flex-shrink: 0; font-size: 14px; line-height: 1;\n}\n.t-remove:hover { background: rgba(239,68,68,.15); color: var(--danger); }\n\n.eq { display: flex; align-items: flex-end; gap: 2px; height: 14px; width: 26px; justify-content: center; }\n.eq i { width: 3px; background: var(--accent); border-radius: 2px; height: 30%; animation: eqbar .9s ease-in-out infinite; }\n.eq i:nth-child(2) { animation-delay: .25s; }\n.eq i:nth-child(3) { animation-delay: .5s; }\n.eq.paused i { animation-play-state: paused; }\n@keyframes eqbar { 0%,100% { height: 25%; } 50% { height: 100%; } }\n\n.empty-state { text-align: center; padding: 40px 20px; color: var(--text-dim); }\n.empty-state .em { font-size: 40px; display: block; margin-bottom: 10px; }\n.empty-state p { font-size: 13.5px; line-height: 1.7; }\n\n/* ---------- Toast ---------- */\n#toast-wrap { position: fixed; left: 50%; bottom: 24px; transform: translateX(-50%); z-index: 999; display: flex; flex-direction: column; gap: 8px; align-items: center; pointer-events: none; }\n.toast {\n    background: var(--card-bg); color: var(--text-main); border-left: 4px solid var(--accent);\n    padding: 11px 18px; border-radius: 10px; box-shadow: var(--shadow); font-size: 13.5px; font-weight: 500;\n    animation: toastIn .25s ease; max-width: 90vw;\n}\n.toast.err { border-left-color: var(--danger); }\n@keyframes toastIn { from { opacity: 0; transform: translateY(14px); } to { opacity: 1; transform: none; } }\n\n/* ---------- Drag overlay ---------- */\n#drop-overlay {\n    position: fixed; inset: 0; background: rgba(15,23,42,.75); z-index: 998;\n    display: grid; place-items: center; color: #fff; font-size: 20px; font-weight: 700;\n    border: 4px dashed var(--accent); backdrop-filter: blur(3px);\n}\n\n/* ---------- Responsive ---------- */\n@media (max-width: 960px) {\n    html, body { overflow: auto; }\n    body { height: auto; min-height: 100vh; }\n    .app-container { height: auto; padding: 14px; gap: 14px; }\n    .main-grid { grid-template-columns: 1fr; }\n    .player-card { overflow: visible; }\n    .album-art { max-height: 220px; width: 220px; margin: 0 auto; }\n    #playlist-items { max-height: 46vh; }\n}\n@media (max-width: 560px) {\n    .app-header { padding: 14px; }\n    .brand { font-size: 19px; }\n    .top-controls { width: 100%; }\n    .top-controls .btn { flex: 1; justify-content: center; }\n    .card { padding: 16px; border-radius: 14px; }\n    .album-art { width: 170px; max-height: 170px; border-radius: 18px; }\n    .track-meta h2 { font-size: 17px; }\n    .ctrl-btn { width: 44px; height: 44px; }\n    .ctrl-btn.main { width: 58px; height: 58px; }\n    .playlist-actions { width: 100%; }\n    .playlist-actions .btn, .playlist-actions .btn-danger { flex: 1; justify-content: center; padding: 9px 8px; font-size: 12.5px; }\n    #playlist-items { max-height: none; }\n}\n</style>\n</head>\n<body>\n\n<div class="app-container">\n\n    <!-- ================= HEADER ================= -->\n    <header class="card app-header">\n        <div class="brand">\n            <span class="logo-dot">♪</span>\n            <span>SonicStream<small>Local Web Music Player</small></span>\n        </div>\n        <div class="top-controls">\n            <button id="theme-toggle" class="btn btn-ghost" type="button">🌙 Mode</button>\n            <label class="btn btn-primary" for="folder-input">📂 Browse Folder</label>\n            <input type="file" id="folder-input" class="hidden" webkitdirectory directory multiple>\n            <input type="file" id="files-input" class="hidden" accept="audio/*" multiple>\n            <input type="file" id="json-input" class="hidden" accept=".json,application/json">\n        </div>\n    </header>\n\n    <!-- ================= MAIN ================= -->\n    <main class="main-grid">\n\n        <!-- ---------- PLAYER ---------- -->\n        <section class="card player-card">\n            <div class="album-art" id="album-art">\n                <svg viewBox="0 0 24 24" xmlns="http://www.w3.org/2000/svg" aria-hidden="true">\n                    <path fill="#ffffff" d="M12 3v10.55A4 4 0 1 0 14 17V7h4V3h-6zm-2 16a2 2 0 1 1 0-4 2 2 0 0 1 0 4z"/>\n                </svg>\n            </div>\n\n            <div class="track-meta">\n                <h2 id="track-title">ยังไม่ได้เลือกเพลง</h2>\n                <p id="track-artist">กดปุ่ม “Browse Folder” เพื่อโหลดเพลงจากเครื่อง</p>\n            </div>\n\n            <div class="progress-container">\n                <span id="current-time">0:00</span>\n                <div class="progress-bar" id="progress-bar">\n                    <div class="progress-fill" id="progress-fill"></div>\n                </div>\n                <span id="total-time">0:00</span>\n            </div>\n\n            <div class="controls">\n                <button class="ctrl-btn" id="btn-prev" type="button" title="ก่อนหน้า" aria-label="Previous">\n                    <svg viewBox="0 0 24 24"><path d="M6 6h2v12H6zm3.5 6 8.5 6V6z"/></svg>\n                </button>\n                <button class="ctrl-btn main" id="btn-play-pause" type="button" title="เล่น / หยุดชั่วคราว" aria-label="Play">\n                    <svg id="icon-play" viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg>\n                    <svg id="icon-pause" class="hidden" viewBox="0 0 24 24"><path d="M6 5h4v14H6zm8 0h4v14h-4z"/></svg>\n                </button>\n                <button class="ctrl-btn" id="btn-next" type="button" title="ถัดไป" aria-label="Next">\n                    <svg viewBox="0 0 24 24"><path d="M16 6h2v12h-2zM6 18l8.5-6L6 6z"/></svg>\n                </button>\n                <button class="ctrl-btn" id="btn-stop" type="button" title="หยุด" aria-label="Stop">\n                    <svg viewBox="0 0 24 24"><path d="M6 6h12v12H6z"/></svg>\n                </button>\n            </div>\n\n            <div class="mode-row">\n                <button class="mode-btn active" id="mode-all" data-mode="all" type="button">🔁 Repeat All</button>\n                <button class="mode-btn" id="mode-one" data-mode="one" type="button">🔂 Repeat One</button>\n                <button class="mode-btn" id="mode-shuffle" data-mode="shuffle" type="button">🔀 Shuffle</button>\n            </div>\n\n            <div class="volume-row">\n                <span class="vol-icon" id="vol-icon" title="ปิด/เปิดเสียง">🔊</span>\n                <input type="range" id="volume" min="0" max="100" value="80" aria-label="Volume">\n                <span id="vol-label" style="font-size:12px;color:var(--text-dim);min-width:34px;text-align:right">80%</span>\n            </div>\n        </section>\n\n        <!-- ---------- PLAYLIST ---------- -->\n        <section class="card playlist-card">\n            <div class="playlist-header">\n                <h3>Playlist <span class="count-badge" id="count-badge">0 tracks</span></h3>\n                <div class="playlist-actions">\n                    <button class="btn btn-soft" id="btn-save-json" type="button">💾 Save JSON</button>\n                    <button class="btn btn-soft" id="btn-import-json" type="button">📥 Import JSON</button>\n                    <button class="btn-danger" id="btn-clear-db" type="button">🗑️ Clear IndexedDB</button>\n                </div>\n            </div>\n            <ul id="playlist-items"></ul>\n        </section>\n\n    </main>\n</div>\n\n<div id="toast-wrap"></div>\n<div id="drop-overlay" class="hidden">🎧 วางไฟล์เพลงที่นี่เพื่อเพิ่มลงเพลย์ลิสต์</div>\n\n<script>\n/* =======================================================================\n   SonicStream — Single File Web Music Player\n   Vanilla JS · IIFE Module Pattern · IndexedDB Session Persistence\n   ======================================================================= */\nconst App = (() => {\n    \'use strict\';\n\n    /* ------------------------- Constants ------------------------- */\n    const DB_NAME    = \'MusicPlayerDB\';\n    const STORE_NAME = \'playlist\';\n    const DB_VERSION = 1;\n    const SESSION_KEY = \'last_session\';\n    const LS_THEME   = \'sonic_theme\';\n    const LS_MODE    = \'sonic_repeat\';\n    const LS_VOL     = \'sonic_volume\';\n    const AUDIO_EXT  = [\'mp3\', \'wav\', \'ogg\', \'oga\', \'m4a\', \'flac\', \'aac\', \'opus\', \'weba\', \'mp4\', \'wma\'];\n\n    /* --------------------------- State --------------------------- */\n    const state = {\n        songs: [],          // { name, file, blobUrl, duration }\n        currentIndex: -1,\n        isPlaying: false,\n        repeatMode: \'all\',  // \'all\' | \'one\' | \'shuffle\'\n        theme: \'light\'\n    };\n\n    let db = null;\n    let isSeeking = false;\n    let shuffleHistory = [];\n    const audio = new Audio();\n    audio.preload = \'metadata\';\n\n    /* --------------------------- DOM ----------------------------- */\n    const $ = (id) => document.getElementById(id);\n    const el = {};\n\n    function cacheDom() {\n        [\n            \'theme-toggle\', \'folder-input\', \'files-input\', \'json-input\', \'album-art\',\n            \'track-title\', \'track-artist\', \'current-time\', \'total-time\',\n            \'progress-bar\', \'progress-fill\', \'btn-prev\', \'btn-play-pause\', \'btn-next\', \'btn-stop\',\n            \'icon-play\', \'icon-pause\', \'mode-all\', \'mode-one\', \'mode-shuffle\',\n            \'volume\', \'vol-icon\', \'vol-label\', \'btn-save-json\', \'btn-import-json\',\n            \'btn-clear-db\', \'playlist-items\', \'count-badge\', \'toast-wrap\', \'drop-overlay\'\n        ].forEach(id => {\n            el[id.replace(/-([a-z])/g, (m, c) => c.toUpperCase())] = $(id);\n        });\n    }\n\n    /* ------------------------- Utilities ------------------------- */\n    function formatTime(sec) {\n        if (!isFinite(sec) || isNaN(sec) || sec < 0) return \'0:00\';\n        const m = Math.floor(sec / 60);\n        const s = Math.floor(sec % 60);\n        return m + \':\' + (s < 10 ? \'0\' + s : s);\n    }\n\n    function isAudioFile(file) {\n        if (!file) return false;\n        if (file.type && file.type.indexOf(\'audio\') === 0) return true;\n        const ext = (file.name.split(\'.\').pop() || \'\').toLowerCase();\n        return AUDIO_EXT.indexOf(ext) !== -1;\n    }\n\n    function parseMeta(name) {\n        const base = String(name || \'\').replace(/\\.[^.]+$/, \'\').replace(/_/g, \' \').trim();\n        const cleaned = base.replace(/^\\s*\\d{1,3}\\s*[-.)]\\s*/, \'\');\n        const parts = cleaned.split(\' - \');\n        if (parts.length >= 2 && parts[0].trim()) {\n            return { artist: parts[0].trim(), title: parts.slice(1).join(\' - \').trim() || cleaned };\n        }\n        return { artist: \'Unknown Artist\', title: cleaned || \'Unknown Track\' };\n    }\n\n    function toast(msg, isError) {\n        const t = document.createElement(\'div\');\n        t.className = \'toast\' + (isError ? \' err\' : \'\');\n        t.textContent = msg;\n        el.toastWrap.appendChild(t);\n        setTimeout(() => {\n            t.style.transition = \'opacity .3s ease, transform .3s ease\';\n            t.style.opacity = \'0\';\n            t.style.transform = \'translateY(10px)\';\n            setTimeout(() => t.remove(), 320);\n        }, 2600);\n    }\n\n    /* ===================================================================\n       INDEXEDDB OPERATIONS\n       =================================================================== */\n    function initDB() {\n        return new Promise((resolve) => {\n            if (!(\'indexedDB\' in window)) {\n                console.warn(\'IndexedDB is not supported in this browser.\');\n                return resolve(null);\n            }\n            let req;\n            try {\n                req = indexedDB.open(DB_NAME, DB_VERSION);\n            } catch (e) {\n                console.warn(\'IndexedDB open failed:\', e);\n                return resolve(null);\n            }\n            req.onupgradeneeded = (e) => {\n                const database = e.target.result;\n                if (!database.objectStoreNames.contains(STORE_NAME)) {\n                    database.createObjectStore(STORE_NAME);\n                }\n            };\n            req.onsuccess = (e) => { db = e.target.result; resolve(db); };\n            req.onerror = (e) => {\n                console.warn(\'IndexedDB error:\', e.target.error);\n                resolve(null);\n            };\n        });\n    }\n\n    function saveToDB(songList) {\n        return new Promise((resolve) => {\n            if (!db) return resolve(false);\n            try {\n                const tx = db.transaction(STORE_NAME, \'readwrite\');\n                const store = tx.objectStore(STORE_NAME);\n                const payload = {\n                    savedAt: new Date().toISOString(),\n                    count: (songList || []).length,\n                    songs: (songList || []).map(s => ({ name: s.name }))\n                };\n                const r = store.put(payload, SESSION_KEY);\n                r.onsuccess = () => resolve(true);\n                r.onerror = () => resolve(false);\n            } catch (e) {\n                console.warn(\'saveToDB failed:\', e);\n                resolve(false);\n            }\n        });\n    }\n\n    function loadFromDB() {\n        return new Promise((resolve) => {\n            if (!db) return resolve(null);\n            try {\n                const tx = db.transaction(STORE_NAME, \'readonly\');\n                const r = tx.objectStore(STORE_NAME).get(SESSION_KEY);\n                r.onsuccess = () => resolve(r.result || null);\n                r.onerror = () => resolve(null);\n            } catch (e) {\n                resolve(null);\n            }\n        });\n    }\n\n    function clearDB() {\n        return new Promise((resolve) => {\n            if (!db) return resolve(false);\n            try {\n                const tx = db.transaction(STORE_NAME, \'readwrite\');\n                const r = tx.objectStore(STORE_NAME).clear();\n                r.onsuccess = () => resolve(true);\n                r.onerror = () => resolve(false);\n            } catch (e) {\n                resolve(false);\n            }\n        });\n    }\n\n    /* ===================================================================\n       OBJECT URL MANAGEMENT\n       =================================================================== */\n    function revokeAllUrls() {\n        state.songs.forEach(s => {\n            if (s.blobUrl) {\n                URL.revokeObjectURL(s.blobUrl);\n                s.blobUrl = null;\n            }\n        });\n    }\n\n    function revokeOtherUrls(keepIndex) {\n        state.songs.forEach((s, i) => {\n            if (i !== keepIndex && s.blobUrl) {\n                URL.revokeObjectURL(s.blobUrl);\n                s.blobUrl = null;\n            }\n        });\n    }\n\n    /* ===================================================================\n       FOLDER / FILE LOADING\n       =================================================================== */\n    function loadFiles(fileList, append) {\n        const files = Array.prototype.slice.call(fileList || []).filter(isAudioFile);\n        if (!files.length) {\n            toast(\'ไม่พบไฟล์เสียงที่รองรับในโฟลเดอร์นี้\', true);\n            return;\n        }\n        files.sort((a, b) => a.name.localeCompare(b.name, undefined, { numeric: true, sensitivity: \'base\' }));\n\n        const newSongs = files.map(f => ({\n            name: f.name,\n            file: f,\n            blobUrl: null,\n            duration: null\n        }));\n\n        if (append && state.songs.length) {\n            state.songs = state.songs.concat(newSongs);\n        } else {\n            stopTrack(true);\n            revokeAllUrls();\n            state.songs = newSongs;\n            state.currentIndex = -1;\n        }\n\n        shuffleHistory = [];\n        renderPlaylist();\n        saveToDB(state.songs);\n        toast(\'โหลดเพลงสำเร็จ \' + newSongs.length + \' เพลง\');\n    }\n\n    /* ===================================================================\n       PLAYBACK ENGINE\n       =================================================================== */\n    function playTrack(index) {\n        if (!state.songs.length) { toast(\'เพลย์ลิสต์ว่าง — กด Browse Folder ก่อน\', true); return; }\n        if (index < 0) index = state.songs.length - 1;\n        if (index >= state.songs.length) index = 0;\n\n        const song = state.songs[index];\n        if (!song) return;\n\n        if (!song.file) {\n            state.currentIndex = index;\n            updateNowPlaying();\n            renderPlaylist();\n            toast(\'เพลงนี้เป็นข้อมูล metadata เท่านั้น — กรุณาโหลดโฟลเดอร์เพื่อเล่นจริง\', true);\n            return;\n        }\n\n        // Same track paused → resume\n        if (index === state.currentIndex && audio.src && song.blobUrl) {\n            audio.play().then(() => {\n                state.isPlaying = true;\n                updatePlayIcon();\n                renderPlaylist();\n            }).catch(err => toast(\'เล่นไม่สำเร็จ: \' + err.message, true));\n            return;\n        }\n\n        // Revoke old object URLs before creating a new one (prevent memory leak)\n        revokeOtherUrls(index);\n        if (song.blobUrl) { URL.revokeObjectURL(song.blobUrl); song.blobUrl = null; }\n        song.blobUrl = URL.createObjectURL(song.file);\n\n        state.currentIndex = index;\n        audio.src = song.blobUrl;\n        audio.load();\n\n        audio.play().then(() => {\n            state.isPlaying = true;\n            updatePlayIcon();\n            updateNowPlaying();\n            renderPlaylist();\n            scrollToActive();\n            updateMediaSession();\n        }).catch(err => {\n            state.isPlaying = false;\n            updatePlayIcon();\n            updateNowPlaying();\n            renderPlaylist();\n            toast(\'ไม่สามารถเล่นไฟล์นี้ได้: \' + err.message, true);\n        });\n    }\n\n    function pauseTrack() {\n        audio.pause();\n        state.isPlaying = false;\n        updatePlayIcon();\n        renderPlaylist();\n        el.albumArt.classList.remove(\'playing\');\n    }\n\n    function togglePlay() {\n        if (!state.songs.length) { toast(\'ยังไม่มีเพลงในเพลย์ลิสต์\', true); return; }\n        if (state.currentIndex === -1) { playTrack(0); return; }\n        if (state.isPlaying) pauseTrack();\n        else playTrack(state.currentIndex);\n    }\n\n    function stopTrack(silent) {\n        audio.pause();\n        try { audio.currentTime = 0; } catch (e) {}\n        state.isPlaying = false;\n        updatePlayIcon();\n        el.progressFill.style.width = \'0%\';\n        el.currentTime.textContent = \'0:00\';\n        el.albumArt.classList.remove(\'playing\');\n        if (!silent) renderPlaylist();\n    }\n\n    function pickShuffleIndex() {\n        const n = state.songs.length;\n        if (n <= 1) return 0;\n        if (shuffleHistory.length >= n) shuffleHistory = [];\n        let idx;\n        let guard = 0;\n        do {\n            idx = Math.floor(Math.random() * n);\n            guard++;\n        } while ((idx === state.currentIndex || shuffleHistory.indexOf(idx) !== -1) && guard < 60);\n        shuffleHistory.push(idx);\n        return idx;\n    }\n\n    function nextTrack() {\n        if (!state.songs.length) return;\n        if (state.repeatMode === \'shuffle\') {\n            playTrack(pickShuffleIndex());\n            return;\n        }\n        let next = state.currentIndex + 1;\n        if (next >= state.songs.length) next = 0; // repeat all → loop to start\n        playTrack(next);\n    }\n\n    function prevTrack() {\n        if (!state.songs.length) return;\n        // Restart current track if played > 3 seconds\n        if (audio.currentTime > 3 && state.currentIndex !== -1) {\n            audio.currentTime = 0;\n            return;\n        }\n        if (state.repeatMode === \'shuffle\') {\n            playTrack(pickShuffleIndex());\n            return;\n        }\n        let prev = state.currentIndex - 1;\n        if (prev < 0) prev = state.songs.length - 1;\n        playTrack(prev);\n    }\n\n    function removeTrack(index) {\n        const song = state.songs[index];\n        if (!song) return;\n        if (song.blobUrl) URL.revokeObjectURL(song.blobUrl);\n        const wasCurrent = index === state.currentIndex;\n        state.songs.splice(index, 1);\n        if (wasCurrent) {\n            stopTrack(true);\n            state.currentIndex = -1;\n            audio.removeAttribute(\'src\');\n            updateNowPlaying();\n        } else if (index < state.currentIndex) {\n            state.currentIndex--;\n        }\n        shuffleHistory = [];\n        renderPlaylist();\n        saveToDB(state.songs);\n    }\n\n    /* ===================================================================\n       UI RENDERING\n       =================================================================== */\n    function updatePlayIcon() {\n        if (state.isPlaying) {\n            el.iconPlay.classList.add(\'hidden\');\n            el.iconPause.classList.remove(\'hidden\');\n            el.btnPlayPause.setAttribute(\'aria-label\', \'Pause\');\n            el.albumArt.classList.add(\'playing\');\n        } else {\n            el.iconPlay.classList.remove(\'hidden\');\n            el.iconPause.classList.add(\'hidden\');\n            el.btnPlayPause.setAttribute(\'aria-label\', \'Play\');\n            el.albumArt.classList.remove(\'playing\');\n        }\n    }\n\n    function updateNowPlaying() {\n        const song = state.songs[state.currentIndex];\n        if (!song) {\n            el.trackTitle.textContent = state.songs.length ? \'พร้อมเล่น\' : \'ยังไม่ได้เลือกเพลง\';\n            el.trackArtist.textContent = state.songs.length\n                ? state.songs.length + \' เพลงในเพลย์ลิสต์ — เลือกเพลงเพื่อเริ่มเล่น\'\n                : \'กดปุ่ม “Browse Folder” เพื่อโหลดเพลงจากเครื่อง\';\n            el.totalTime.textContent = \'0:00\';\n            el.currentTime.textContent = \'0:00\';\n            el.progressFill.style.width = \'0%\';\n            document.title = \'SonicStream — Web Music Player\';\n            return;\n        }\n        const meta = parseMeta(song.name);\n        el.trackTitle.textContent = meta.title;\n        el.trackTitle.title = song.name;\n        el.trackArtist.textContent = meta.artist + (song.file ? \'\' : \' · (metadata only)\');\n        document.title = \'▶ \' + meta.title + \' — SonicStream\';\n    }\n\n    function renderPlaylist() {\n        const ul = el.playlistItems;\n        ul.innerHTML = \'\';\n        el.countBadge.textContent = state.songs.length + (state.songs.length === 1 ? \' track\' : \' tracks\');\n\n        if (!state.songs.length) {\n            const li = document.createElement(\'li\');\n            li.className = \'empty-state\';\n            li.innerHTML = \'<span class="em">🎵</span><p><strong>ยังไม่มีเพลงในเพลย์ลิสต์</strong><br>\' +\n                \'กด “📂 Browse Folder” เพื่อเลือกโฟลเดอร์เพลง<br>หรือลากไฟล์เพลงมาวางบนหน้าจอนี้ได้เลย</p>\';\n            ul.appendChild(li);\n            return;\n        }\n\n        const frag = document.createDocumentFragment();\n        state.songs.forEach((song, i) => {\n            const meta = parseMeta(song.name);\n            const li = document.createElement(\'li\');\n            li.className = \'track-item\' + (i === state.currentIndex ? \' active\' : \'\') + (song.file ? \'\' : \' missing\');\n            li.dataset.index = String(i);\n\n            const idx = document.createElement(\'div\');\n            idx.className = \'t-index\';\n            if (i === state.currentIndex) {\n                idx.innerHTML = \'<span class="eq\' + (state.isPlaying ? \'\' : \' paused\') + \'"><i></i><i></i><i></i></span>\';\n            } else {\n                idx.textContent = String(i + 1);\n            }\n\n            const info = document.createElement(\'div\');\n            info.className = \'t-info\';\n            const t = document.createElement(\'div\');\n            t.className = \'t-title\';\n            t.textContent = meta.title;\n            const s = document.createElement(\'div\');\n            s.className = \'t-sub\';\n            s.textContent = meta.artist + (song.file ? \'\' : \' · ไม่มีไฟล์เสียง\');\n            info.appendChild(t);\n            info.appendChild(s);\n\n            const dur = document.createElement(\'div\');\n            dur.className = \'t-dur\';\n            dur.textContent = song.duration ? formatTime(song.duration) : \'--:--\';\n\n            const rm = document.createElement(\'button\');\n            rm.className = \'t-remove\';\n            rm.type = \'button\';\n            rm.title = \'ลบออกจากเพลย์ลิสต์\';\n            rm.textContent = \'✕\';\n            rm.addEventListener(\'click\', (ev) => {\n                ev.stopPropagation();\n                removeTrack(i);\n            });\n\n            li.appendChild(idx);\n            li.appendChild(info);\n            li.appendChild(dur);\n            li.appendChild(rm);\n            li.addEventListener(\'click\', () => playTrack(i));\n            frag.appendChild(li);\n        });\n        ul.appendChild(frag);\n    }\n\n    function scrollToActive() {\n        const active = el.playlistItems.querySelector(\'.track-item.active\');\n        if (active && active.scrollIntoView) {\n            active.scrollIntoView({ block: \'nearest\', behavior: \'smooth\' });\n        }\n    }\n\n    function updateMediaSession() {\n        if (!(\'mediaSession\' in navigator)) return;\n        const song = state.songs[state.currentIndex];\n        if (!song) return;\n        const meta = parseMeta(song.name);\n        try {\n            navigator.mediaSession.metadata = new MediaMetadata({\n                title: meta.title, artist: meta.artist, album: \'SonicStream\'\n            });\n            navigator.mediaSession.setActionHandler(\'play\', () => playTrack(state.currentIndex));\n            navigator.mediaSession.setActionHandler(\'pause\', pauseTrack);\n            navigator.mediaSession.setActionHandler(\'previoustrack\', prevTrack);\n            navigator.mediaSession.setActionHandler(\'nexttrack\', nextTrack);\n            navigator.mediaSession.setActionHandler(\'stop\', () => stopTrack(false));\n        } catch (e) { /* ignore unsupported handlers */ }\n    }\n\n    /* ===================================================================\n       THEME\n       =================================================================== */\n    function applyTheme(theme) {\n        state.theme = theme === \'dark\' ? \'dark\' : \'light\';\n        document.documentElement.setAttribute(\'data-theme\', state.theme);\n        el.themeToggle.textContent = state.theme === \'dark\' ? \'☀️ Mode\' : \'🌙 Mode\';\n        try { localStorage.setItem(LS_THEME, state.theme); } catch (e) {}\n    }\n\n    function toggleTheme() {\n        applyTheme(state.theme === \'dark\' ? \'light\' : \'dark\');\n    }\n\n    /* ===================================================================\n       REPEAT MODE\n       =================================================================== */\n    function setRepeatMode(mode) {\n        state.repeatMode = mode;\n        shuffleHistory = [];\n        [el.modeAll, el.modeOne, el.modeShuffle].forEach(b => {\n            b.classList.toggle(\'active\', b.dataset.mode === mode);\n        });\n        audio.loop = false; // handled manually in \'ended\'\n        try { localStorage.setItem(LS_MODE, mode); } catch (e) {}\n    }\n\n    /* ===================================================================\n       SEEKING\n       =================================================================== */\n    function seekFromEvent(e) {\n        const rect = el.progressBar.getBoundingClientRect();\n        const clientX = (e.touches && e.touches[0]) ? e.touches[0].clientX : e.clientX;\n        let ratio = (clientX - rect.left) / rect.width;\n        ratio = Math.max(0, Math.min(1, ratio));\n        el.progressFill.style.width = (ratio * 100) + \'%\';\n        if (isFinite(audio.duration) && audio.duration > 0) {\n            const time = ratio * audio.duration;\n            el.currentTime.textContent = formatTime(time);\n            return time;\n        }\n        return null;\n    }\n\n    function bindSeekEvents() {\n        const bar = el.progressBar;\n\n        const onDown = (e) => {\n            if (!audio.src || !isFinite(audio.duration)) return;\n            isSeeking = true;\n            bar.classList.add(\'dragging\');\n            seekFromEvent(e);\n            e.preventDefault();\n        };\n        const onMove = (e) => {\n            if (!isSeeking) return;\n            seekFromEvent(e);\n            e.preventDefault();\n        };\n        const onUp = (e) => {\n            if (!isSeeking) return;\n            const time = seekFromEvent(e);\n            if (time !== null) audio.currentTime = time;\n            isSeeking = false;\n            bar.classList.remove(\'dragging\');\n        };\n\n        bar.addEventListener(\'mousedown\', onDown);\n        document.addEventListener(\'mousemove\', onMove);\n        document.addEventListener(\'mouseup\', onUp);\n\n        bar.addEventListener(\'touchstart\', onDown, { passive: false });\n        document.addEventListener(\'touchmove\', onMove, { passive: false });\n        document.addEventListener(\'touchend\', (e) => {\n            if (!isSeeking) return;\n            if (isFinite(audio.duration) && audio.duration > 0) {\n                const ratio = parseFloat(el.progressFill.style.width) / 100;\n                audio.currentTime = Math.max(0, Math.min(1, ratio)) * audio.duration;\n            }\n            isSeeking = false;\n            bar.classList.remove(\'dragging\');\n        });\n    }\n\n    /* ===================================================================\n       JSON EXPORT / IMPORT / CLEAR\n       =================================================================== */\n    function exportJSON() {\n        if (!state.songs.length) { toast(\'ไม่มีเพลงให้บันทึก\', true); return; }\n        const data = {\n            app: \'SonicStream\',\n            version: 1,\n            exportedAt: new Date().toISOString(),\n            repeatMode: state.repeatMode,\n            count: state.songs.length,\n            songs: state.songs.map((s, i) => {\n                const m = parseMeta(s.name);\n                return { index: i + 1, name: s.name, title: m.title, artist: m.artist, duration: s.duration || null };\n            })\n        };\n        const blob = new Blob([JSON.stringify(data, null, 2)], { type: \'application/json\' });\n        const url = URL.createObjectURL(blob);\n        const a = document.createElement(\'a\');\n        a.href = url;\n        a.download = \'playlist.json\';\n        document.body.appendChild(a);\n        a.click();\n        document.body.removeChild(a);\n        setTimeout(() => URL.revokeObjectURL(url), 1500);\n        toast(\'บันทึก playlist.json เรียบร้อย\');\n    }\n\n    function importJSON(file) {\n        if (!file) return;\n        const reader = new FileReader();\n        reader.onload = (e) => {\n            try {\n                const parsed = JSON.parse(e.target.result);\n                let list = [];\n                if (Array.isArray(parsed)) list = parsed;\n                else if (parsed && Array.isArray(parsed.songs)) list = parsed.songs;\n                else throw new Error(\'รูปแบบไฟล์ไม่ถูกต้อง\');\n\n                const imported = list.map(item => {\n                    const name = typeof item === \'string\'\n                        ? item\n                        : (item.name || item.title || \'Unknown Track\');\n                    return { name: String(name), file: null, blobUrl: null, duration: item && item.duration ? item.duration : null };\n                }).filter(s => s.name);\n\n                if (!imported.length) throw new Error(\'ไม่พบรายการเพลงในไฟล์\');\n\n                // Try to re-link existing loaded files by filename\n                const existing = {};\n                state.songs.forEach(s => { if (s.file) existing[s.name] = s.file; });\n                imported.forEach(s => { if (existing[s.name]) s.file = existing[s.name]; });\n\n                stopTrack(true);\n                revokeAllUrls();\n                state.songs = imported;\n                state.currentIndex = -1;\n                shuffleHistory = [];\n                audio.removeAttribute(\'src\');\n\n                if (parsed && parsed.repeatMode) setRepeatMode(parsed.repeatMode);\n\n                renderPlaylist();\n                updateNowPlaying();\n                saveToDB(state.songs);\n                toast(\'นำเข้าเพลย์ลิสต์ \' + imported.length + \' รายการแล้ว\');\n            } catch (err) {\n                toast(\'อ่านไฟล์ JSON ไม่สำเร็จ: \' + err.message, true);\n            }\n        };\n        reader.onerror = () => toast(\'อ่านไฟล์ไม่สำเร็จ\', true);\n        reader.readAsText(file);\n    }\n\n    function handleClearDB() {\n        if (!confirm(\'ต้องการล้างข้อมูลใน IndexedDB และรีเซ็ตเพลย์ลิสต์ทั้งหมดหรือไม่?\')) return;\n        clearDB().then((ok) => {\n            stopTrack(true);\n            revokeAllUrls();\n            state.songs = [];\n            state.currentIndex = -1;\n            state.isPlaying = false;\n            shuffleHistory = [];\n            audio.removeAttribute(\'src\');\n            audio.load();\n\n            el.currentTime.textContent = \'0:00\';\n            el.totalTime.textContent = \'0:00\';\n            el.progressFill.style.width = \'0%\';\n            el.folderInput.value = \'\';\n            el.filesInput.value = \'\';\n            el.jsonInput.value = \'\';\n\n            updatePlayIcon();\n            updateNowPlaying();\n            renderPlaylist();\n            toast(ok ? \'ล้าง IndexedDB และรีเซ็ตเรียบร้อยแล้ว\' : \'รีเซ็ตเพลย์ลิสต์แล้ว (IndexedDB ไม่พร้อมใช้งาน)\');\n        });\n    }\n\n    /* ===================================================================\n       AUDIO EVENT BINDING\n       =================================================================== */\n    function bindAudioEvents() {\n        audio.addEventListener(\'loadedmetadata\', () => {\n            el.totalTime.textContent = formatTime(audio.duration);\n            const song = state.songs[state.currentIndex];\n            if (song && isFinite(audio.duration)) {\n                song.duration = audio.duration;\n                const item = el.playlistItems.querySelector(\'.track-item[data-index="\' + state.currentIndex + \'"] .t-dur\');\n                if (item) item.textContent = formatTime(audio.duration);\n            }\n        });\n\n        audio.addEventListener(\'timeupdate\', () => {\n            if (isSeeking) return;\n            const dur = audio.duration;\n            if (isFinite(dur) && dur > 0) {\n                el.progressFill.style.width = ((audio.currentTime / dur) * 100) + \'%\';\n            }\n            el.currentTime.textContent = formatTime(audio.currentTime);\n        });\n\n        audio.addEventListener(\'play\', () => {\n            state.isPlaying = true;\n            updatePlayIcon();\n        });\n\n        audio.addEventListener(\'pause\', () => {\n            state.isPlaying = false;\n            updatePlayIcon();\n        });\n\n        audio.addEventListener(\'ended\', () => {\n            if (state.repeatMode === \'one\') {\n                audio.currentTime = 0;\n                audio.play().catch(() => {});\n                return;\n            }\n            if (state.repeatMode === \'shuffle\') {\n                playTrack(pickShuffleIndex());\n                return;\n            }\n            // \'all\' → loop back to start when reaching the end\n            let next = state.currentIndex + 1;\n            if (next >= state.songs.length) next = 0;\n            playTrack(next);\n        });\n\n        audio.addEventListener(\'error\', () => {\n            if (!audio.src) return;\n            toast(\'เกิดข้อผิดพลาดขณะเล่นไฟล์เสียง\', true);\n            state.isPlaying = false;\n            updatePlayIcon();\n        });\n    }\n\n    /* ===================================================================\n       VOLUME\n       =================================================================== */\n    function applyVolume(v) {\n        const val = Math.max(0, Math.min(100, parseInt(v, 10) || 0));\n        audio.volume = val / 100;\n        audio.muted = val === 0;\n        el.volume.value = String(val);\n        el.volLabel.textContent = val + \'%\';\n        el.volIcon.textContent = val === 0 ? \'🔇\' : (val < 50 ? \'🔉\' : \'🔊\');\n        try { localStorage.setItem(LS_VOL, String(val)); } catch (e) {}\n    }\n\n    /* ===================================================================\n       DRAG & DROP\n       =================================================================== */\n    function bindDragDrop() {\n        let counter = 0;\n        window.addEventListener(\'dragenter\', (e) => {\n            e.preventDefault();\n            counter++;\n            el.dropOverlay.classList.remove(\'hidden\');\n        });\n        window.addEventListener(\'dragover\', (e) => e.preventDefault());\n        window.addEventListener(\'dragleave\', (e) => {\n            e.preventDefault();\n            counter--;\n            if (counter <= 0) { counter = 0; el.dropOverlay.classList.add(\'hidden\'); }\n        });\n        window.addEventListener(\'drop\', (e) => {\n            e.preventDefault();\n            counter = 0;\n            el.dropOverlay.classList.add(\'hidden\');\n            if (e.dataTransfer && e.dataTransfer.files && e.dataTransfer.files.length) {\n                loadFiles(e.dataTransfer.files, true);\n            }\n        });\n    }\n\n    /* ===================================================================\n       KEYBOARD SHORTCUTS\n       =================================================================== */\n    function bindKeyboard() {\n        document.addEventListener(\'keydown\', (e) => {\n            const tag = (e.target.tagName || \'\').toLowerCase();\n            if (tag === \'input\' || tag === \'textarea\' || e.target.isContentEditable) return;\n            switch (e.code) {\n                case \'Space\': e.preventDefault(); togglePlay(); break;\n                case \'ArrowRight\': e.preventDefault();\n                    if (audio.src) audio.currentTime = Math.min(audio.duration || 0, audio.currentTime + 5);\n                    break;\n                case \'ArrowLeft\': e.preventDefault();\n                    if (audio.src) audio.currentTime = Math.max(0, audio.currentTime - 5);\n                    break;\n                case \'ArrowUp\': e.preventDefault(); applyVolume(parseInt(el.volume.value, 10) + 5); break;\n                case \'ArrowDown\': e.preventDefault(); applyVolume(parseInt(el.volume.value, 10) - 5); break;\n                case \'KeyN\': nextTrack(); break;\n                case \'KeyP\': prevTrack(); break;\n                case \'KeyS\': stopTrack(false); break;\n                default: break;\n            }\n        });\n    }\n\n    /* ===================================================================\n       EVENT BINDING\n       =================================================================== */\n    function bindUI() {\n        el.themeToggle.addEventListener(\'click\', toggleTheme);\n\n        el.folderInput.addEventListener(\'change\', (e) => {\n            loadFiles(e.target.files, false);\n            e.target.value = \'\';\n        });\n        el.filesInput.addEventListener(\'change\', (e) => {\n            loadFiles(e.target.files, true);\n            e.target.value = \'\';\n        });\n\n        el.btnPlayPause.addEventListener(\'click\', togglePlay);\n        el.btnPrev.addEventListener(\'click\', prevTrack);\n        el.btnNext.addEventListener(\'click\', nextTrack);\n        el.btnStop.addEventListener(\'click\', () => stopTrack(false));\n\n        [el.modeAll, el.modeOne, el.modeShuffle].forEach(btn => {\n            btn.addEventListener(\'click\', () => setRepeatMode(btn.dataset.mode));\n        });\n\n        el.volume.addEventListener(\'input\', (e) => applyVolume(e.target.value));\n        el.volIcon.addEventListener(\'click\', () => {\n            const cur = parseInt(el.volume.value, 10);\n            applyVolume(cur === 0 ? 80 : 0);\n        });\n\n        el.btnSaveJson.addEventListener(\'click\', exportJSON);\n        el.btnImportJson.addEventListener(\'click\', () => el.jsonInput.click());\n        el.jsonInput.addEventListener(\'change\', (e) => {\n            importJSON(e.target.files && e.target.files[0]);\n            e.target.value = \'\';\n        });\n        el.btnClearDb.addEventListener(\'click\', handleClearDB);\n\n        window.addEventListener(\'beforeunload\', revokeAllUrls);\n    }\n\n    /* ===================================================================\n       INIT\n       =================================================================== */\n    function restorePrefs() {\n        let theme = \'light\';\n        try { theme = localStorage.getItem(LS_THEME) || (window.matchMedia && window.matchMedia(\'(prefers-color-scheme: dark)\').matches ? \'dark\' : \'light\'); } catch (e) {}\n        applyTheme(theme);\n\n        let mode = \'all\';\n        try { mode = localStorage.getItem(LS_MODE) || \'all\'; } catch (e) {}\n        setRepeatMode([\'all\', \'one\', \'shuffle\'].indexOf(mode) !== -1 ? mode : \'all\');\n\n        let vol = 80;\n        try {\n            const v = localStorage.getItem(LS_VOL);\n            if (v !== null) vol = parseInt(v, 10);\n        } catch (e) {}\n        applyVolume(vol);\n    }\n\n    function init() {\n        cacheDom();\n        restorePrefs();\n        bindUI();\n        bindAudioEvents();\n        bindSeekEvents();\n        bindDragDrop();\n        bindKeyboard();\n        renderPlaylist();\n        updateNowPlaying();\n        updatePlayIcon();\n\n        initDB().then(() => loadFromDB()).then((session) => {\n            if (session && session.songs && session.songs.length) {\n                state.songs = session.songs.map(s => ({\n                    name: s.name, file: null, blobUrl: null, duration: null\n                }));\n                renderPlaylist();\n                updateNowPlaying();\n                toast(\'กู้คืนเพลย์ลิสต์เดิม \' + state.songs.length + \' รายการ (โหลดโฟลเดอร์เพื่อเล่นไฟล์จริง)\');\n            }\n        }).catch(() => {});\n    }\n\n    if (document.readyState === \'loading\') {\n        document.addEventListener(\'DOMContentLoaded\', init);\n    } else {\n        init();\n    }\n\n    /* ------------------------ Public API ------------------------- */\n    return {\n        state, initDB, saveToDB, loadFromDB, clearDB,\n        playTrack, pauseTrack, stopTrack, nextTrack, prevTrack,\n        exportJSON, importJSON, setRepeatMode, applyTheme, formatTime\n    };\n})();\n</script>\n</body>\n</html>'
GAME_HUB_HTML = '<!DOCTYPE html>\n<html lang="th"><head>\n<meta http-equiv="X-UA-Compatible" content="IE=edge">\n<meta charset="utf-8">\n<title>Time Machine Game Hub</title>\n<style>\nhtml,body{margin:0;padding:0}\nbody.tm{font-family:"Segoe UI",Tahoma,Arial,sans-serif;font-size:14px;line-height:1.45}\nbody.dark{background:#1e1f22;color:#e6e6e6}\nbody.light{background:#f4f5f7;color:#1c1e21}\n.wrap{max-width:980px;margin:0 auto;padding:16px}\nh1{font-size:22px;margin:6px 0 14px}\nh2{font-size:17px;margin:4px 0 8px}\na{color:#4c8dff}\n.card{padding:14px;margin:0 0 14px 0;border-radius:8px}\nbody.dark .card{background:#2b2d31;border:1px solid #3d4046}\nbody.light .card{background:#fff;border:1px solid #c9ccd1}\n.row{margin:8px 0}\nlabel{margin-right:14px}\ntextarea,input.txt,select{box-sizing:border-box;font:13px Consolas,"Courier New",monospace;padding:8px;border-radius:6px}\ntextarea{width:100%;min-height:150px;resize:vertical}\nbody.dark textarea,body.dark input.txt,body.dark select{background:#1a1b1e;color:#e6e6e6;border:1px solid #4a4d52}\nbody.light textarea,body.light input.txt,body.light select{background:#fff;color:#1c1e21;border:1px solid #b5b9c0}\ntextarea.bad{border-color:#e5534b !important}\nbutton.btn{font:13px "Segoe UI",Arial,sans-serif;padding:7px 14px;margin:0 6px 6px 0;border-radius:6px;cursor:pointer;border:1px solid #4c8dff;background:#1a66e0;color:#fff}\nbutton.btn.sec{background:transparent;color:inherit;border-color:#7a7f87}\nbutton.btn.on{background:#1a66e0;color:#fff;border-color:#4c8dff}\nbutton.btn:disabled{opacity:.45;cursor:default}\n.msg{min-height:20px;margin-top:6px}\n.err{color:#e5534b}.ok{color:#3fb950}\nbody.light .err{color:#c62828}body.light .ok{color:#1b7f37}\n.drop{border:2px dashed #7a7f87;border-radius:8px;padding:26px;text-align:center}\n.drop.over{border-color:#4c8dff;background:rgba(76,141,255,.12)}\n.preview{max-width:100%;max-height:320px;margin-top:10px;border-radius:6px}\n.small{font-size:12px;opacity:.8}\n.game{display:inline-block;vertical-align:top;width:31%;margin:0 1% 14px 1%;box-sizing:border-box;text-align:center}\n.game svg{width:96px;height:96px}\n.game a.btn{display:inline-block;text-decoration:none;margin-top:8px}\n#cv{width:100%;max-width:800px;display:block;border:1px solid #7a7f87;border-radius:6px;background:#fff}\n.hud{margin:8px 0;font-size:16px}\ntable.oth{border-collapse:collapse;margin:10px auto;background:#2e7d32}\ntable.oth td{width:48px;height:48px;border:1px solid #1b5e20;text-align:center;vertical-align:middle;padding:0;cursor:pointer}\n.disc{width:36px;height:36px;border-radius:50%;margin:0 auto}\n.disc.b{background:#111;border:1px solid #000}\n.disc.w{background:#fff;border:1px solid #999}\n.disc.h{width:10px;height:10px;background:rgba(255,255,255,.5)}\ntable.ttt{border-collapse:collapse;margin:10px auto}\ntable.ttt td{width:90px;height:90px;border:2px solid #7a7f87;text-align:center;font-size:52px;font-weight:bold;cursor:pointer}\n.center{text-align:center}\n</style>\n</head>\n<body class="tm dark">\n<div class="wrap">\n  <h1>NEUTRON GAME HUB</h1>\n  <div class="card game">\n    <svg viewBox="0 0 96 96"><rect x="0" y="80" width="96" height="3" fill="#888"/><rect x="14" y="48" width="26" height="30" fill="#4c8dff"/><rect x="28" y="34" width="22" height="16" fill="#4c8dff"/><rect x="42" y="38" width="4" height="4" fill="#fff"/><rect x="66" y="52" width="9" height="28" fill="#3fb950"/></svg>\n    <h2>Duck Runner</h2><div class="small">กระโดดข้ามกระบองเพชร 3 ชีวิต เก็บ Top 5</div>\n    <a class="btn" data-href="duck.html" href="#">เล่น / Play</a>\n  </div>\n  <div class="card game">\n    <svg viewBox="0 0 96 96"><rect x="8" y="8" width="80" height="80" fill="#2e7d32"/><circle cx="36" cy="36" r="14" fill="#111"/><circle cx="60" cy="36" r="14" fill="#fff"/><circle cx="36" cy="60" r="14" fill="#fff"/><circle cx="60" cy="60" r="14" fill="#111"/></svg>\n    <h2>Othello / Reversi</h2><div class="small">กระดาน 8x8 เล่น 2 คนหรือกับ AI</div>\n    <a class="btn" data-href="othello.html" href="#">เล่น / Play</a>\n  </div>\n  <div class="card game">\n    <svg viewBox="0 0 96 96"><g stroke="#888" stroke-width="3"><line x1="34" y1="8" x2="34" y2="88"/><line x1="62" y1="8" x2="62" y2="88"/><line x1="8" y1="34" x2="88" y2="34"/><line x1="8" y1="62" x2="88" y2="62"/></g><text x="12" y="30" font-size="24" fill="#4c8dff">X</text><text x="40" y="58" font-size="24" fill="#e5534b">O</text><text x="66" y="86" font-size="24" fill="#4c8dff">X</text></svg>\n    <h2>Tic-Tac-Toe (OX)</h2><div class="small">3x3 เล่น 2 คนหรือกับ AI</div>\n    <a class="btn" data-href="tictactoe.html" href="#">เล่น / Play</a>\n  </div>\n  \n  <div class="card game">\n    <svg viewBox="0 0 1200 675" xmlns="http://www.w3.org/2000/svg">\n  <defs>\n    <!-- Background Space Gradient -->\n    <radialGradient id="space-bg" cx="70%" cy="40%" r="80%">\n      <stop offset="0%" stop-color="#0a1026" />\n      <stop offset="60%" stop-color="#030611" />\n      <stop offset="100%" stop-color="#000205" />\n    </radialGradient>\n\n    <!-- Earth Atmosphere Glow -->\n    <radialGradient id="atmosphere" cx="0%" cy="50%" r="60%">\n      <stop offset="70%" stop-color="#3b9eff" stop-opacity="0.4" />\n      <stop offset="95%" stop-color="#4facfe" stop-opacity="0.1" />\n      <stop offset="100%" stop-color="#000000" stop-opacity="0" />\n    </radialGradient>\n\n    <!-- Earth Body -->\n    <radialGradient id="earth-globe" cx="30%" cy="30%" r="70%">\n      <stop offset="0%" stop-color="#2b82c9" />\n      <stop offset="40%" stop-color="#1b4d82" />\n      <stop offset="80%" stop-color="#0d2347" />\n      <stop offset="100%" stop-color="#030a17" />\n    </radialGradient>\n\n    <!-- Engine Thruster Main Flame -->\n    <linearGradient id="thruster-flame-main" x1="1" y1="0" x2="0" y2="0">\n      <stop offset="0%" stop-color="#ffffff" />\n      <stop offset="20%" stop-color="#9ee5ff" />\n      <stop offset="50%" stop-color="#3b82f6" />\n      <stop offset="80%" stop-color="#1d4ed8" stop-opacity="0.6" />\n      <stop offset="100%" stop-color="#1e1b4b" stop-opacity="0" />\n    </linearGradient>\n\n    <!-- Thruster Core Flame -->\n    <linearGradient id="thruster-core" x1="1" y1="0" x2="0" y2="0">\n      <stop offset="0%" stop-color="#ffffff" />\n      <stop offset="30%" stop-color="#fdba74" />\n      <stop offset="70%" stop-color="#f97316" />\n      <stop offset="100%" stop-color="#ef4444" stop-opacity="0" />\n    </linearGradient>\n\n    <!-- Hull Metallic Gradient -->\n    <linearGradient id="hull-base" x1="0" y1="0" x2="0" y2="1">\n      <stop offset="0%" stop-color="#ffffff" />\n      <stop offset="25%" stop-color="#e2e8f0" />\n      <stop offset="60%" stop-color="#cbd5e1" />\n      <stop offset="85%" stop-color="#94a3b8" />\n      <stop offset="100%" stop-color="#64748b" />\n    </linearGradient>\n\n    <linearGradient id="hull-dark" x1="0" y1="0" x2="0" y2="1">\n      <stop offset="0%" stop-color="#475569" />\n      <stop offset="50%" stop-color="#334155" />\n      <stop offset="100%" stop-color="#1e293b" />\n    </linearGradient>\n\n    <linearGradient id="solar-panel" x1="0" y1="0" x2="1" y2="0">\n      <stop offset="0%" stop-color="#1e3a8a" />\n      <stop offset="50%" stop-color="#2563eb" />\n      <stop offset="100%" stop-color="#1d4ed8" />\n    </linearGradient>\n\n    <linearGradient id="cockpit-glass" x1="0" y1="0" x2="1" y2="1">\n      <stop offset="0%" stop-color="#0f172a" />\n      <stop offset="40%" stop-color="#1e293b" />\n      <stop offset="100%" stop-color="#0284c7" />\n    </linearGradient>\n\n    <!-- Shadow overlay for 3D volume -->\n    <linearGradient id="bottom-shadow" x1="0" y1="0" x2="0" y2="1">\n      <stop offset="0%" stop-color="#000000" stop-opacity="0" />\n      <stop offset="60%" stop-color="#000000" stop-opacity="0.3" />\n      <stop offset="100%" stop-color="#000000" stop-opacity="0.75" />\n    </linearGradient>\n\n    <!-- Glow Filter -->\n    <filter id="glow" x="-20%" y="-20%" width="140%" height="140%">\n      <feGaussianBlur stdDeviation="12" result="blur" />\n      <feComposite in="SourceGraphic" in2="blur" operator="over" />\n    </filter>\n    \n    <filter id="intense-glow" x="-50%" y="-50%" width="200%" height="200%">\n      <feGaussianBlur stdDeviation="8" result="blur1" />\n      <feGaussianBlur stdDeviation="25" result="blur2" />\n      <feMerge>\n        <feMergeNode in="blur2" />\n        <feMergeNode in="blur1" />\n        <feMergeNode in="SourceGraphic" />\n      </feMerge>\n    </filter>\n  </defs>\n\n  <!-- ================= BACKGROUND & STARS ================= -->\n  <rect width="1200" height="675" fill="url(#space-bg)" />\n\n  <!-- Stars Field -->\n  <g fill="#ffffff">\n    <circle cx="100" cy="80" r="0.8" opacity="0.8" />\n    <circle cx="250" cy="40" r="1.5" opacity="0.9" />\n    <circle cx="420" cy="120" r="0.6" opacity="0.5" />\n    <circle cx="550" cy="60" r="1.2" opacity="0.7" />\n    <circle cx="680" cy="150" r="0.8" opacity="0.4" />\n    <circle cx="810" cy="50" r="1.8" opacity="0.9" />\n    <circle cx="960" cy="110" r="0.7" opacity="0.6" />\n    <circle cx="1120" cy="70" r="1.3" opacity="0.8" />\n\n    <circle cx="70" cy="220" r="1.1" opacity="0.6" />\n    <circle cx="310" cy="190" r="0.7" opacity="0.5" />\n    <circle cx="750" cy="240" r="1.4" opacity="0.8" />\n    <circle cx="1050" cy="200" r="0.9" opacity="0.7" />\n\n    <circle cx="150" cy="520" r="1.2" opacity="0.7" />\n    <circle cx="380" cy="600" r="0.8" opacity="0.4" />\n    <circle cx="520" cy="560" r="1.6" opacity="0.9" />\n    <circle cx="710" cy="620" r="0.6" opacity="0.6" />\n    <circle cx="890" cy="540" r="1.2" opacity="0.8" />\n    <circle cx="1150" cy="590" r="1.5" opacity="0.7" />\n    \n    <!-- Cross stars -->\n    <path d="M810,45 L810,55 M805,50 L815,50" stroke="#fff" stroke-width="0.6" opacity="0.7" />\n    <path d="M250,35 L250,45 M245,40 L255,40" stroke="#fff" stroke-width="0.5" opacity="0.6" />\n  </g>\n\n  <!-- Moon in background -->\n  <g transform="translate(260, 140)">\n    <circle cx="0" cy="0" r="28" fill="#e2e8f0" />\n    <circle cx="-6" cy="-4" r="28" fill="#090d1a" /> <!-- Moon Shadow -->\n    <circle cx="4" cy="-8" r="4" fill="#cbd5e1" opacity="0.5" />\n    <circle cx="12" cy="6" r="6" fill="#cbd5e1" opacity="0.4" />\n    <circle cx="-2" cy="12" r="3" fill="#cbd5e1" opacity="0.4" />\n  </g>\n\n  <!-- Earth (Bottom Left Corner) -->\n  <g transform="translate(-150, 480)">\n    <circle cx="200" cy="200" r="380" fill="url(#earth-globe)" />\n    <!-- Earth Atmosphere Rim -->\n    <circle cx="200" cy="200" r="386" fill="none" stroke="url(#atmosphere)" stroke-width="12" />\n    <!-- Continents & Clouds (Stylized) -->\n    <path d="M 120 50 Q 180 80 220 30 Q 300 70 280 150 Q 200 180 140 120 Z" fill="#3b82f6" opacity="0.4" />\n    <path d="M 50 180 Q 120 160 160 240 Q 100 290 30 220 Z" fill="#22c55e" opacity="0.25" />\n    <!-- Swirling Clouds -->\n    <path d="M 80 100 Q 200 40 320 120 Q 220 100 80 100 Z" fill="#ffffff" opacity="0.3" />\n    <path d="M 20 220 Q 150 180 280 280 Q 140 240 20 220 Z" fill="#ffffff" opacity="0.25" />\n  </g>\n\n  <!-- ================= THRUSTER FLAMES (LEFT) ================= -->\n  <g filter="url(#intense-glow)">\n    <!-- Main Plumes (Exhaust Stream) -->\n    <ellipse cx="140" cy="265" rx="180" ry="42" fill="url(#thruster-flame-main)" />\n    <ellipse cx="140" cy="340" rx="220" ry="55" fill="url(#thruster-flame-main)" />\n    <ellipse cx="140" cy="415" rx="180" ry="42" fill="url(#thruster-flame-main)" />\n\n    <!-- Core Shock Diamonds / Hot Flame -->\n    <polygon points="340,265 180,250 80,265 180,280" fill="url(#thruster-core)" />\n    <polygon points="350,340 160,320 40,340 160,360" fill="url(#thruster-core)" />\n    <polygon points="340,415 180,400 80,415 180,430" fill="url(#thruster-core)" />\n    \n    <!-- White Hot Core Points -->\n    <ellipse cx="320" cy="265" rx="40" ry="12" fill="#ffffff" />\n    <ellipse cx="330" cy="340" rx="55" ry="18" fill="#ffffff" />\n    <ellipse cx="320" cy="415" rx="40" ry="12" fill="#ffffff" />\n  </g>\n\n\n  <!-- ================= MAIN SPACESHIP STRUCTURE ================= -->\n  <g id="spaceship">\n\n    <!-- 1. MECHANICAL PIPING & ENGINE BAY (REAR / LEFT) -->\n    <g id="engine-greebles">\n      <!-- Deep Engine Structure Base -->\n      <rect x="330" y="240" width="80" height="200" fill="#1e293b" rx="5" />\n\n      <!-- Complex Mechanical Pipes & Tubes -->\n      <path d="M 320 250 L 370 250 L 370 430 L 320 430" stroke="#475569" stroke-width="8" fill="none" />\n      <path d="M 310 270 C 350 270 350 310 380 310" stroke="#94a3b8" stroke-width="4" fill="none" />\n      <path d="M 310 410 C 350 410 350 370 380 370" stroke="#94a3b8" stroke-width="4" fill="none" />\n      <path d="M 330 290 L 390 290 M 330 390 L 390 390" stroke="#cbd5e1" stroke-width="5" fill="none" />\n\n      <!-- Copper/Gold Fuel Lines -->\n      <path d="M 320 280 L 360 280 L 360 330 L 400 330" stroke="#d97706" stroke-width="3" fill="none" />\n      <path d="M 320 400 L 360 400 L 360 350 L 400 350" stroke="#d97706" stroke-width="3" fill="none" />\n      <path d="M 340 240 L 340 440" stroke="#b45309" stroke-width="3" stroke-dasharray="8,4" fill="none" />\n\n      <!-- Engine Nozzles (3 Huge Nozzles) -->\n      <!-- Top Nozzle -->\n      <path d="M 310 240 L 350 250 L 350 280 L 310 290 Z" fill="#334155" stroke="#94a3b8" stroke-width="2" />\n      <rect x="300" y="245" width="10" height="40" fill="#0f172a" stroke="#64748b" />\n      <!-- Middle Main Nozzle -->\n      <path d="M 290 310 L 350 320 L 350 360 L 290 370 Z" fill="#1e293b" stroke="#cbd5e1" stroke-width="2" />\n      <rect x="280" y="318" width="12" height="44" fill="#020617" stroke="#94a3b8" />\n      <!-- Bottom Nozzle -->\n      <path d="M 310 390 L 350 400 L 350 430 L 310 440 Z" fill="#334155" stroke="#94a3b8" stroke-width="2" />\n      <rect x="300" y="395" width="10" height="40" fill="#0f172a" stroke="#64748b" />\n\n      <!-- Small RCS Thruster Nozzles (Top/Bottom Angle) -->\n      <path d="M 360 215 L 375 200 L 385 208 L 370 220 Z" fill="#475569" />\n      <path d="M 360 465 L 375 480 L 385 472 L 370 460 Z" fill="#475569" />\n    </g>\n\n    <!-- 2. REAR WINGS / STABILIZERS -->\n    <!-- Top Rear Wing -->\n    <polygon points="380,240 280,180 340,170 440,220" fill="url(#hull-base)" stroke="#94a3b8" />\n    <polygon points="340,170 440,220 430,225 335,175" fill="#334155" />\n    <!-- Bottom Rear Wing -->\n    <polygon points="380,440 280,500 340,510 440,460" fill="url(#hull-base)" stroke="#64748b" />\n    <polygon points="380,440 280,500 295,502 390,443" fill="#1e293b" />\n\n    <!-- 3. MAIN HULL BODY (MID-SECTION) -->\n    <!-- Main Outer Silhouette -->\n    <path d="M 400 220 \n             L 580 200 \n             L 750 230 \n             L 920 290 \n             L 1080 340 \n             L 980 390 \n             L 780 430 \n             L 550 460 \n             L 400 450 Z" fill="url(#hull-base)" stroke="#cbd5e1" stroke-width="2" />\n\n    <!-- Hull Armor Plating & Panel Lines -->\n    <!-- Upper Hull Block -->\n    <path d="M 420 220 L 580 200 L 720 230 L 700 320 L 420 320 Z" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.5" />\n    <!-- Mid Section Block -->\n    <path d="M 420 325 L 700 325 L 880 335 L 750 430 L 420 420 Z" fill="#e2e8f0" stroke="#94a3b8" stroke-width="1.5" />\n    <!-- Lower Shadowed Hull -->\n    <path d="M 400 420 L 750 430 L 980 390 L 850 445 L 550 460 Z" fill="url(#hull-dark)" />\n\n    <!-- Detail Panels (Greeble rectangles on hull) -->\n    <rect x="450" y="240" width="40" height="25" fill="#cbd5e1" stroke="#94a3b8" />\n    <rect x="500" y="235" width="60" height="30" fill="#cbd5e1" stroke="#94a3b8" />\n    <rect x="570" y="230" width="45" height="35" fill="#94a3b8" stroke="#64748b" />\n    <rect x="450" y="280" width="90" height="20" fill="#e2e8f0" stroke="#94a3b8" />\n    <rect x="550" y="280" width="70" height="20" fill="#cbd5e1" stroke="#94a3b8" />\n    \n    <rect x="440" y="340" width="50" height="40" fill="#cbd5e1" stroke="#94a3b8" />\n    <rect x="500" y="340" width="80" height="25" fill="#cbd5e1" stroke="#94a3b8" />\n    <rect x="590" y="340" width="60" height="45" fill="#94a3b8" stroke="#475569" />\n\n    <!-- Reinforced Maintenance Hatches -->\n    <circle cx="680" cy="280" r="8" fill="#475569" stroke="#94a3b8" stroke-width="2" />\n    <circle cx="680" cy="370" r="10" fill="#334155" stroke="#94a3b8" stroke-width="2" />\n\n    <!-- 4. SOLAR PANELS & RADIATORS (MID TOP & BOTTOM) -->\n    <!-- Mid Solar Panel Wing (Extending Side-ways) -->\n    <g id="solar-array">\n      <rect x="620" y="310" width="140" height="28" fill="url(#solar-panel)" stroke="#475569" stroke-width="2" rx="2" transform="skewX(-15)" />\n      <!-- Grid Lines on Solar Panel -->\n      <line x1="650" y1="310" x2="640" y2="338" stroke="#60a5fa" stroke-width="1.5" />\n      <line x1="680" y1="310" x2="670" y2="338" stroke="#60a5fa" stroke-width="1.5" />\n      <line x1="710" y1="310" x2="700" y2="338" stroke="#60a5fa" stroke-width="1.5" />\n      <line x1="740" y1="310" x2="730" y2="338" stroke="#60a5fa" stroke-width="1.5" />\n      <line x1="615" y1="324" x2="750" y2="324" stroke="#60a5fa" stroke-width="1" />\n    </g>\n\n    <!-- 5. TOP MODULES & ANTENNAS -->\n    <!-- Radar Dish -->\n    <path d="M 520 185 C 510 165 540 155 550 175 Z" fill="#cbd5e1" stroke="#475569" stroke-width="2" />\n    <line x1="535" y1="170" x2="545" y2="160" stroke="#ef4444" stroke-width="2" /> <!-- Feed Horn -->\n    <line x1="530" y1="180" x2="530" y2="200" stroke="#64748b" stroke-width="3" /> <!-- Mount -->\n\n    <!-- Communication Antennas SPIKES -->\n    <line x1="490" y1="210" x2="490" y2="140" stroke="#cbd5e1" stroke-width="2" />\n    <circle cx="490" cy="140" r="3" fill="#ef4444" /> <!-- Beacon Light -->\n    <line x1="500" y1="210" x2="505" y2="160" stroke="#94a3b8" stroke-width="1.5" />\n    <line x1="720" y1="230" x2="735" y2="180" stroke="#cbd5e1" stroke-width="2" />\n\n    <!-- Sensor Domes -->\n    <path d="M 640 195 A 14 14 0 0 1 668 195 Z" fill="#e2e8f0" stroke="#64748b" stroke-width="2" />\n    <path d="M 770 240 A 10 10 0 0 1 790 240 Z" fill="#e2e8f0" stroke="#64748b" stroke-width="2" />\n\n    <!-- 6. FORWARD CABIN & COCKPIT (NOSE / RIGHT) -->\n    <!-- Forward Hull Transition -->\n    <path d="M 720 230 L 860 270 L 980 320 L 920 380 L 750 430 Z" fill="#f8fafc" stroke="#cbd5e1" />\n\n    <!-- Nose Cone -->\n    <path d="M 940 305 L 1090 340 Q 1110 345 1090 350 L 930 380 Z" fill="url(#hull-base)" stroke="#cbd5e1" stroke-width="1.5" />\n    <!-- Black Heat Shield Tip on Nose -->\n    <path d="M 1050 331 L 1090 340 Q 1100 345 1090 350 L 1045 357 Z" fill="#0f172a" />\n\n    <!-- Cockpit Windows (Bridge) -->\n    <!-- Main Front Visor -->\n    <polygon points="910,305 970,315 965,330 905,320" fill="url(#cockpit-glass)" stroke="#475569" stroke-width="2" />\n    <!-- Side Windows Row -->\n    <polygon points="870,300 895,303 892,315 868,312" fill="url(#cockpit-glass)" stroke="#475569" stroke-width="1.5" />\n    <polygon points="840,296 860,299 858,310 838,307" fill="url(#cockpit-glass)" stroke="#475569" stroke-width="1.5" />\n    <!-- Porthole Windows -->\n    <circle cx="815" cy="303" r="5" fill="url(#cockpit-glass)" stroke="#64748b" stroke-width="1.5" />\n    <circle cx="790" cy="300" r="5" fill="url(#cockpit-glass)" stroke="#64748b" stroke-width="1.5" />\n\n    <!-- 7. DECALS AND IDENTIFICATION DETAILS -->\n    <!-- Insignia Logo (Star & Circle) -->\n    <g transform="translate(830, 340)">\n      <circle cx="15" cy="15" r="14" fill="#1e3a8a" stroke="#3b82f6" stroke-width="1.5" />\n      <path d="M 15 5 L 18 12 L 25 15 L 18 18 L 15 25 L 12 18 L 5 15 L 12 12 Z" fill="#ffffff" />\n    </g>\n    <!-- Ship Name Text -->\n    <text x="865" y="350" font-family="monospace, sans-serif" font-weight="bold" font-size="13" fill="#0f172a" letter-spacing="2">AURORA</text>\n    <text x="865" y="362" font-family="monospace, sans-serif" font-weight="bold" font-size="9" fill="#2563eb" letter-spacing="1.5">EXPLORER</text>\n\n    <!-- Red Danger/Warning Stripe Lines -->\n    <path d="M 430 250 L 440 240 L 445 240 L 435 250 Z" fill="#ef4444" />\n    <path d="M 445 250 L 455 240 L 460 240 L 450 250 Z" fill="#ef4444" />\n    <line x1="930" y1="365" x2="970" y2="355" stroke="#ef4444" stroke-width="2" />\n\n    <!-- 8. BOTTOM TURRETS & DOCKING PORTS -->\n    <!-- Lower Docking Ring -->\n    <rect x="680" y="425" width="40" height="12" fill="#334155" stroke="#94a3b8" stroke-width="1.5" rx="3" />\n    <line x1="700" y1="425" x2="700" y2="437" stroke="#cbd5e1" stroke-width="2" />\n\n    <!-- Defense Turret (Bottom) -->\n    <path d="M 820 405 A 12 12 0 0 1 844 405 Z" fill="#475569" stroke="#1e293b" />\n    <line x1="828" y1="410" x2="820" y2="422" stroke="#0f172a" stroke-width="3" />\n    <line x1="834" y1="410" x2="826" y2="422" stroke="#0f172a" stroke-width="3" />\n\n    <!-- Forward Sensor Array / Cannons -->\n    <line x1="940" y1="380" x2="980" y2="385" stroke="#94a3b8" stroke-width="2.5" />\n    <line x1="945" y1="385" x2="975" y2="390" stroke="#64748b" stroke-width="2" />\n\n    <!-- Global Lighting & Shadow Overlay for 3D realism -->\n    <path d="M 400 360 \n             L 700 365 \n             L 920 360 \n             L 1090 350 \n             L 980 390 \n             L 780 430 \n             L 550 460 \n             L 400 450 Z" fill="url(#bottom-shadow)" style="mix-blend-mode: multiply;" />\n\n    <!-- Top Edge Highlight Glow Line -->\n    <path d="M 400 220 L 580 200 L 750 230 L 920 290 L 1080 340" fill="none" stroke="#ffffff" stroke-width="2" opacity="0.6" />\n  </g>\n\n  <!-- Navigation Lights / Warning Beacons (Glowing) -->\n  <g filter="url(#glow)">\n    <!-- Red Light Top Rear -->\n    <circle cx="340" cy="170" r="4" fill="#ef4444" />\n    <!-- Green Light Bottom Rear -->\n    <circle cx="340" cy="510" r="4" fill="#22c55e" />\n    <!-- Blue Strobe Nose -->\n    <circle cx="1070" cy="338" r="3" fill="#38bdf8" />\n  </g>\n</svg>\n    <h2>Stellar Raid</h2><div class="small">Stellar Raid เกมยานยิงพิ้ว ๆ</div>\n    <a class="btn" data-href="Stellar.html" href="#">เล่น / Play</a>\n  </div>\n  \n</div>\n<script>\nvar TM = (function () {\n  var api = {};\n  api.$ = function (id) { return document.getElementById(id); };\n\n  api.param = function (name) {\n    var m = new RegExp(\'[?&]\' + name + \'=([^&]*)\').exec(location.search);\n    return m ? decodeURIComponent(m[1]) : null;\n  };\n\n  api.setTheme = function (t) {\n    t = (t === \'light\') ? \'light\' : \'dark\';\n    document.body.className = \'tm \' + t;\n  };\n\n  api.xhr = function (method, url, body, cb) {\n    var x = new XMLHttpRequest();\n    var sep = url.indexOf(\'?\') < 0 ? \'?\' : \'&\';\n    x.open(method, url + sep + \'_=\' + new Date().getTime(), true);  // defeat IE XHR caching\n    x.onreadystatechange = function () {\n      if (x.readyState === 4) { cb(x.status >= 200 && x.status < 300, x.responseText); }\n    };\n    if (body !== null) { x.setRequestHeader(\'Content-Type\', \'application/json\'); }\n    x.send(body);\n  };\n\n  api.pollTheme = function () {\n    function tick() {\n      api.xhr(\'GET\', \'/api/theme\', null, function (ok, txt) {\n        if (ok) { try { api.setTheme(JSON.parse(txt).theme); } catch (e) {} }\n      });\n    }\n    setInterval(tick, 1500);\n  };\n\n  // Persistent store: server-side JSON (Data/GameScores), localStorage only as fallback.\n  api.store = {\n    load: function (key, cb) {\n      api.xhr(\'GET\', \'/api/store/\' + key, null, function (ok, txt) {\n        if (ok) { try { cb(JSON.parse(txt)); return; } catch (e) {} }\n        try { cb(JSON.parse(localStorage.getItem(\'tm_\' + key) || \'{}\')); } catch (e2) { cb({}); }\n      });\n    },\n    save: function (key, obj, cb) {\n      api.xhr(\'POST\', \'/api/store/\' + key, JSON.stringify(obj), function (ok, txt) {\n        if (!ok) { try { localStorage.setItem(\'tm_\' + key, JSON.stringify(obj)); } catch (e) {} }\n        if (cb) { cb(ok); }\n      });\n    }\n  };\n\n  api.copyText = function (text, cb) {\n    function fallback() {\n      var t = document.createElement(\'textarea\');\n      t.value = text; t.style.position = \'fixed\'; t.style.opacity = \'0\';\n      document.body.appendChild(t); t.select();\n      var ok = false;\n      try { ok = document.execCommand(\'copy\'); } catch (e) {}\n      document.body.removeChild(t); cb(ok);\n    }\n    if (window.clipboardData && window.clipboardData.setData) {\n      try { window.clipboardData.setData(\'Text\', text); cb(true); return; } catch (e) {}\n    }\n    if (navigator.clipboard && navigator.clipboard.writeText) {\n      navigator.clipboard.writeText(text).then(function () { cb(true); }, fallback);\n      return;\n    }\n    fallback();\n  };\n\n  api.downloadBytes = function (bytes, name, mime) {\n    var blob;\n    try { blob = new Blob([bytes], { type: mime || \'application/octet-stream\' }); } catch (e) { return false; }\n    if (navigator.msSaveOrOpenBlob) { navigator.msSaveOrOpenBlob(blob, name); return true; }\n    var url = URL.createObjectURL(blob), a = document.createElement(\'a\');\n    a.href = url; a.download = name; document.body.appendChild(a); a.click(); document.body.removeChild(a);\n    setTimeout(function () { URL.revokeObjectURL(url); }, 15000);\n    return true;\n  };\n\n  api.preventFileDrop = function () {\n    function stop(e) { if (e.preventDefault) { e.preventDefault(); } return false; }\n    document.addEventListener(\'dragover\', stop, false);\n    document.addEventListener(\'drop\', stop, false);\n  };\n\n  api.hubLink = function (href) { return href + location.search; };\n\n  api.init = function () {\n    api.setTheme(api.param(\'theme\') || \'dark\');\n    api.pollTheme();\n  };\n  return api;\n})();\n</script>\n\n<script>\n(function () {\n  TM.init();\n  var links = document.getElementsByTagName(\'a\'), i;\n  for (i = 0; i < links.length; i++) {\n    var h = links[i].getAttribute(\'data-href\');\n    if (h) { links[i].href = TM.hubLink(h); }\n  }\n})();\n</script>\n</body></html>'
DUCK_HTML = '<!DOCTYPE html>\n<html lang="th"><head>\n<meta http-equiv="X-UA-Compatible" content="IE=edge">\n<meta charset="utf-8">\n<title>Duck Runner</title>\n<style>\nhtml,body{margin:0;padding:0}\nbody.tm{font-family:"Segoe UI",Tahoma,Arial,sans-serif;font-size:14px;line-height:1.45}\nbody.dark{background:#1e1f22;color:#e6e6e6}\nbody.light{background:#f4f5f7;color:#1c1e21}\n.wrap{max-width:980px;margin:0 auto;padding:16px}\nh1{font-size:22px;margin:6px 0 14px}\nh2{font-size:17px;margin:4px 0 8px}\na{color:#4c8dff}\n.card{padding:14px;margin:0 0 14px 0;border-radius:8px}\nbody.dark .card{background:#2b2d31;border:1px solid #3d4046}\nbody.light .card{background:#fff;border:1px solid #c9ccd1}\n.row{margin:8px 0}\nlabel{margin-right:14px}\ntextarea,input.txt,select{box-sizing:border-box;font:13px Consolas,"Courier New",monospace;padding:8px;border-radius:6px}\ntextarea{width:100%;min-height:150px;resize:vertical}\nbody.dark textarea,body.dark input.txt,body.dark select{background:#1a1b1e;color:#e6e6e6;border:1px solid #4a4d52}\nbody.light textarea,body.light input.txt,body.light select{background:#fff;color:#1c1e21;border:1px solid #b5b9c0}\ntextarea.bad{border-color:#e5534b !important}\nbutton.btn{font:13px "Segoe UI",Arial,sans-serif;padding:7px 14px;margin:0 6px 6px 0;border-radius:6px;cursor:pointer;border:1px solid #4c8dff;background:#1a66e0;color:#fff}\nbutton.btn.sec{background:transparent;color:inherit;border-color:#7a7f87}\nbutton.btn.on{background:#1a66e0;color:#fff;border-color:#4c8dff}\nbutton.btn:disabled{opacity:.45;cursor:default}\n.msg{min-height:20px;margin-top:6px}\n.err{color:#e5534b}.ok{color:#3fb950}\nbody.light .err{color:#c62828}body.light .ok{color:#1b7f37}\n.drop{border:2px dashed #7a7f87;border-radius:8px;padding:26px;text-align:center}\n.drop.over{border-color:#4c8dff;background:rgba(76,141,255,.12)}\n.preview{max-width:100%;max-height:320px;margin-top:10px;border-radius:6px}\n.small{font-size:12px;opacity:.8}\n.game{display:inline-block;vertical-align:top;width:31%;margin:0 1% 14px 1%;box-sizing:border-box;text-align:center}\n.game svg{width:96px;height:96px}\n.game a.btn{display:inline-block;text-decoration:none;margin-top:8px}\n#cv{width:100%;max-width:800px;display:block;border:1px solid #7a7f87;border-radius:6px;background:#fff}\n.hud{margin:8px 0;font-size:16px}\ntable.oth{border-collapse:collapse;margin:10px auto;background:#2e7d32}\ntable.oth td{width:48px;height:48px;border:1px solid #1b5e20;text-align:center;vertical-align:middle;padding:0;cursor:pointer}\n.disc{width:36px;height:36px;border-radius:50%;margin:0 auto}\n.disc.b{background:#111;border:1px solid #000}\n.disc.w{background:#fff;border:1px solid #999}\n.disc.h{width:10px;height:10px;background:rgba(255,255,255,.5)}\ntable.ttt{border-collapse:collapse;margin:10px auto}\ntable.ttt td{width:90px;height:90px;border:2px solid #7a7f87;text-align:center;font-size:52px;font-weight:bold;cursor:pointer}\n.center{text-align:center}\n</style>\n</head>\n<body class="tm dark">\n<div class="wrap">\n  <a id="back" href="#">&larr; Game Hub</a>\n  <h1>Duck Runner</h1>\n  <div class="hud">Score: <b id="score">0</b> &nbsp; Lives: <b id="lives">♥♥♥</b> &nbsp;\n    <span class="small">Space / ↑ / คลิก = กระโดด • Enter / R = เริ่มใหม่</span> &nbsp; <button id="muteBtn" class="btn sec" type="button" style="padding:3px 10px;font-size:12px">🔊 เสียง: เปิด</button></div>\n  <canvas id="cv" width="800" height="240"></canvas>\n  <div id="over" class="card" style="display:none;margin-top:12px">\n    <h2>Game Over — <span id="final">0</span></h2>\n    <div id="entry" class="row">ชื่อ: <input id="name" class="txt" type="text" maxlength="12" value="Player" style="width:160px">\n      <button id="save" class="btn" type="button">บันทึกคะแนน</button></div>\n    <button id="again" class="btn sec" type="button">เล่นอีกครั้ง (Restart)</button>\n  </div>\n  <div class="card" style="margin-top:12px"><h2>Top 5</h2><ol id="hs"></ol></div>\n</div>\n<script>\nvar TM = (function () {\n  var api = {};\n  api.$ = function (id) { return document.getElementById(id); };\n\n  api.param = function (name) {\n    var m = new RegExp(\'[?&]\' + name + \'=([^&]*)\').exec(location.search);\n    return m ? decodeURIComponent(m[1]) : null;\n  };\n\n  api.setTheme = function (t) {\n    t = (t === \'light\') ? \'light\' : \'dark\';\n    document.body.className = \'tm \' + t;\n  };\n\n  api.xhr = function (method, url, body, cb) {\n    var x = new XMLHttpRequest();\n    var sep = url.indexOf(\'?\') < 0 ? \'?\' : \'&\';\n    x.open(method, url + sep + \'_=\' + new Date().getTime(), true);  // defeat IE XHR caching\n    x.onreadystatechange = function () {\n      if (x.readyState === 4) { cb(x.status >= 200 && x.status < 300, x.responseText); }\n    };\n    if (body !== null) { x.setRequestHeader(\'Content-Type\', \'application/json\'); }\n    x.send(body);\n  };\n\n  api.pollTheme = function () {\n    function tick() {\n      api.xhr(\'GET\', \'/api/theme\', null, function (ok, txt) {\n        if (ok) { try { api.setTheme(JSON.parse(txt).theme); } catch (e) {} }\n      });\n    }\n    setInterval(tick, 1500);\n  };\n\n  // Persistent store: server-side JSON (Data/GameScores), localStorage only as fallback.\n  api.store = {\n    load: function (key, cb) {\n      api.xhr(\'GET\', \'/api/store/\' + key, null, function (ok, txt) {\n        if (ok) { try { cb(JSON.parse(txt)); return; } catch (e) {} }\n        try { cb(JSON.parse(localStorage.getItem(\'tm_\' + key) || \'{}\')); } catch (e2) { cb({}); }\n      });\n    },\n    save: function (key, obj, cb) {\n      api.xhr(\'POST\', \'/api/store/\' + key, JSON.stringify(obj), function (ok, txt) {\n        if (!ok) { try { localStorage.setItem(\'tm_\' + key, JSON.stringify(obj)); } catch (e) {} }\n        if (cb) { cb(ok); }\n      });\n    }\n  };\n\n  api.copyText = function (text, cb) {\n    function fallback() {\n      var t = document.createElement(\'textarea\');\n      t.value = text; t.style.position = \'fixed\'; t.style.opacity = \'0\';\n      document.body.appendChild(t); t.select();\n      var ok = false;\n      try { ok = document.execCommand(\'copy\'); } catch (e) {}\n      document.body.removeChild(t); cb(ok);\n    }\n    if (window.clipboardData && window.clipboardData.setData) {\n      try { window.clipboardData.setData(\'Text\', text); cb(true); return; } catch (e) {}\n    }\n    if (navigator.clipboard && navigator.clipboard.writeText) {\n      navigator.clipboard.writeText(text).then(function () { cb(true); }, fallback);\n      return;\n    }\n    fallback();\n  };\n\n  api.downloadBytes = function (bytes, name, mime) {\n    var blob;\n    try { blob = new Blob([bytes], { type: mime || \'application/octet-stream\' }); } catch (e) { return false; }\n    if (navigator.msSaveOrOpenBlob) { navigator.msSaveOrOpenBlob(blob, name); return true; }\n    var url = URL.createObjectURL(blob), a = document.createElement(\'a\');\n    a.href = url; a.download = name; document.body.appendChild(a); a.click(); document.body.removeChild(a);\n    setTimeout(function () { URL.revokeObjectURL(url); }, 15000);\n    return true;\n  };\n\n  api.preventFileDrop = function () {\n    function stop(e) { if (e.preventDefault) { e.preventDefault(); } return false; }\n    document.addEventListener(\'dragover\', stop, false);\n    document.addEventListener(\'drop\', stop, false);\n  };\n\n  api.hubLink = function (href) { return href + location.search; };\n\n  api.init = function () {\n    api.setTheme(api.param(\'theme\') || \'dark\');\n    api.pollTheme();\n  };\n  return api;\n})();\n\n\n\n(function () {\n  var $ = TM.$, cv = $(\'cv\'), g = cv.getContext(\'2d\'), W = cv.width, H = cv.height, GY = H - 36;\n  var GRAV = 1900, JUMPV = 660, DW = 34, DH = 40, DX = 56;\n  var s, last = Date.now(), scores = [], saved = false;\n  TM.init(); TM.preventFileDrop();\n  $(\'back\').href = TM.hubLink(\'game_hub.html\');\n  var raf = window.requestAnimationFrame || function (f) { return setTimeout(f, 16); };\n\n  var SFX = (function () {\n    var ctx = null, muted = false, bgmTimer = null, stepIdx = 0;\n    var melody = [261.63, 329.63, 392.00, 523.25, 392.00, 329.63, 293.66, 349.23, 440.00, 587.33, 440.00, 349.23];\n    function ensure() {\n      if (!ctx) {\n        var AC = window.AudioContext || window.webkitAudioContext;\n        if (AC) { try { ctx = new AC(); } catch (e) {} }\n      }\n      if (ctx && ctx.state === \'suspended\') { try { ctx.resume(); } catch (e) {} }\n      return ctx;\n    }\n    function tone(freq, dur, type, vol, slideTo) {\n      if (muted) return;\n      var c = ensure(); if (!c) return;\n      try {\n        var o = c.createOscillator(), g = c.createGain(), now = c.currentTime;\n        o.type = type || \'square\';\n        o.frequency.setValueAtTime(freq, now);\n        if (slideTo) { o.frequency.exponentialRampToValueAtTime(slideTo, now + dur); }\n        g.gain.setValueAtTime(vol || 0.08, now);\n        g.gain.exponentialRampToValueAtTime(0.0001, now + dur);\n        o.connect(g); g.connect(c.destination);\n        o.start(now); o.stop(now + dur + 0.02);\n      } catch (e) {}\n    }\n    function startBGM() {\n      ensure();\n      if (bgmTimer) return;\n      bgmTimer = setInterval(function () {\n        if (muted || !s || !s.started || s.over) return;\n        var f = melody[stepIdx % melody.length];\n        stepIdx++;\n        tone(f, 0.14, \'triangle\', 0.035);\n      }, 180);\n    }\n    function stopBGM() {\n      if (bgmTimer) { clearInterval(bgmTimer); bgmTimer = null; }\n    }\n    return {\n      startBGM: startBGM,\n      stopBGM: stopBGM,\n      jump: function () { startBGM(); tone(320, 0.14, \'square\', 0.09, 680); },\n      hit: function () {\n        tone(160, 0.22, \'sawtooth\', 0.14, 70);\n        setTimeout(function () { tone(110, 0.18, \'square\', 0.10, 55); }, 60);\n      },\n      die: function () {\n        stopBGM();\n        var notes = [392, 349.23, 329.63, 261.63, 196, 130.81];\n        for (var i = 0; i < notes.length; i++) {\n          (function (idx) {\n            setTimeout(function () { tone(notes[idx], 0.18, \'sawtooth\', 0.13, notes[idx] * 0.85); }, idx * 110);\n          })(i);\n        }\n      },\n      toggleMute: function () {\n        muted = !muted;\n        if (!muted) ensure();\n        return muted;\n      }\n    };\n  })();\n\n  $(\'muteBtn\').onclick = function () { var m = SFX.toggleMute(); $(\'muteBtn\').textContent = m ? \'🔇 เสียง: ปิด\' : \'🔊 เสียง: เปิด\'; };\n\n  function rnd(a, b) { return a + Math.random() * (b - a); }\n  function reset() {\n    s = { y: 0, vy: 0, obs: [], dist: 0, speed: 300, lives: 3, inv: 0, gap: 500, since: 0, over: false, started: false };\n    saved = false; $(\'over\').style.display = \'none\';\n  }\n  function score() { return Math.floor(s.dist / 10); }\n\n  function jump() {\n    if (s.over) { return; }\n    var wasGrounded = (s.y === 0);\n    s.started = true;\n    SFX.startBGM();\n    if (wasGrounded) { s.vy = JUMPV; SFX.jump(); }\n  }\n\n  function hit(o) {\n    var dx = DX + 6, dy = GY - s.y - DH + 6, dw = DW - 12, dh = DH - 10;\n    return dx < o.x + o.w && dx + dw > o.x && dy < GY && dy + dh > GY - o.h;\n  }\n\n  function step(dt) {\n    if (!s.started || s.over) { return; }\n    s.speed = 300 + Math.min(380, s.dist / 30);\n    s.dist += s.speed * dt;\n    s.vy -= GRAV * dt; s.y += s.vy * dt;\n    if (s.y <= 0) { s.y = 0; s.vy = 0; }\n    s.since += s.speed * dt;\n    if (s.since >= s.gap) {\n      s.obs.push({ x: W + 10, w: Math.floor(rnd(16, 30)), h: Math.floor(rnd(28, 52)) });\n      s.since = 0; s.gap = rnd(1.1, 2.0) * s.speed;\n    }\n    var i, o;\n    for (i = s.obs.length - 1; i >= 0; i--) {\n      s.obs[i].x -= s.speed * dt;\n      if (s.obs[i].x + s.obs[i].w < 0) { s.obs.splice(i, 1); }\n    }\n    if (s.inv > 0) { s.inv -= dt; return; }\n    for (i = 0; i < s.obs.length; i++) {\n      o = s.obs[i];\n      if (hit(o)) {\n        s.lives--; s.inv = 1.5; s.obs.splice(i, 1);\n        if (s.lives <= 0) { SFX.hit(); gameOver(); } else { SFX.hit(); }\n        break;\n      }\n    }\n  }\n\n  function draw() {\n    var dark = document.body.className.indexOf(\'dark\') >= 0;\n    var bg = dark ? \'#1a1b1e\' : \'#ffffff\', fg = dark ? \'#e6e6e6\' : \'#333333\', i, o, top, leg;\n    g.fillStyle = bg; g.fillRect(0, 0, W, H);\n    g.fillStyle = fg; g.fillRect(0, GY, W, 2);\n    for (i = 0; i < 12; i++) { g.fillRect(((i * 97) - (s.dist % 97) + 970) % W, GY + 8 + (i % 3) * 6, 10, 2); }\n    g.fillStyle = \'#3fb950\';\n    for (i = 0; i < s.obs.length; i++) {\n      o = s.obs[i];\n      g.fillRect(o.x, GY - o.h, o.w, o.h);\n      g.fillRect(o.x - 5, GY - o.h * 0.65, 5, 5); g.fillRect(o.x + o.w, GY - o.h * 0.5, 5, 5);\n    }\n    if (!(s.inv > 0 && Math.floor(s.inv * 10) % 2 === 0)) {\n      top = GY - s.y - DH; leg = s.y > 0 ? 0 : (Math.floor(s.dist / 25) % 2) * 4;\n      g.fillStyle = \'#4c8dff\';\n      g.fillRect(DX, top + 14, DW - 6, DH - 22);\n      g.fillRect(DX + 12, top, DW - 12, 18);\n      g.fillRect(DX + 4, top + DH - 8, 7, 8 - leg); g.fillRect(DX + 18, top + DH - 8, 7, 4 + leg);\n      g.fillStyle = bg; g.fillRect(DX + DW - 10, top + 4, 4, 4);\n    }\n    g.fillStyle = fg; g.font = \'14px Segoe UI, Arial\';\n    if (!s.started) { g.fillText(\'กด Space หรือคลิกเพื่อเริ่ม / Press Space or click to start\', 200, 100); }\n  }\n\n  function hud() {\n    $(\'score\').textContent = score();\n    var h = \'\', i; for (i = 0; i < 3; i++) { h += i < s.lives ? \'♥\' : \'♡\'; }\n    $(\'lives\').textContent = h;\n  }\n\n  function sanitize(d) {\n    var a = (d && d.scores && d.scores.length !== undefined) ? d.scores : [], out = [], i;\n    for (i = 0; i < a.length; i++) {\n      if (a[i] && typeof a[i].score === \'number\') { out.push({ name: String(a[i].name || \'Player\').substring(0, 16), score: a[i].score, date: String(a[i].date || \'\') }); }\n    }\n    out.sort(function (x, y) { return y.score - x.score; });\n    return out.slice(0, 5);\n  }\n  function renderScores() {\n    var ol = $(\'hs\'), i, li;\n    while (ol.firstChild) { ol.removeChild(ol.firstChild); }\n    if (!scores.length) { li = document.createElement(\'li\'); li.textContent = \'—\'; ol.appendChild(li); }\n    for (i = 0; i < scores.length; i++) {\n      li = document.createElement(\'li\');\n      li.textContent = scores[i].name + \' — \' + scores[i].score + (scores[i].date ? \'  (\' + scores[i].date + \')\' : \'\');\n      ol.appendChild(li);\n    }\n  }\n\n  function gameOver() {\n    s.over = true;\n    SFX.die();\n    var sc = score(), qualifies = sc > 0 && (scores.length < 5 || sc > scores[scores.length - 1].score);\n    $(\'final\').textContent = sc;\n    $(\'entry\').style.display = qualifies ? \'\' : \'none\';\n    $(\'over\').style.display = \'block\';\n  }\n\n  $(\'save\').onclick = function () {\n    if (saved) { return; }\n    saved = true;\n    scores.push({ name: ($(\'name\').value || \'Player\').substring(0, 12), score: score(), date: new Date().toISOString().substring(0, 10) });\n    scores = sanitize({ scores: scores });\n    renderScores(); $(\'entry\').style.display = \'none\';\n    TM.store.save(\'dino\', { scores: scores });\n  };\n  $(\'again\').onclick = reset;\n\n  document.addEventListener(\'keydown\', function (e) {\n    var k = e.keyCode, tag = e.target && e.target.tagName;\n    if (tag === \'INPUT\') { return; }\n    if (k === 32 || k === 38) { if (e.preventDefault) { e.preventDefault(); } jump(); }\n    else if (k === 13 || k === 82) { reset(); }\n  }, false);\n  cv.addEventListener(\'mousedown\', jump, false);\n  cv.addEventListener(\'touchstart\', function (e) { if (e.preventDefault) { e.preventDefault(); } jump(); }, false);\n\n  function loop() {\n    var now = Date.now(), dt = Math.min(0.05, (now - last) / 1000);\n    last = now; step(dt); draw(); hud(); raf(loop);\n  }\n  reset();\n  TM.store.load(\'dino\', function (d) { scores = sanitize(d); renderScores(); });\n  raf(loop);\n})();\n\n</script>\n</body></html>'
OTHELLO_HTML = '<!DOCTYPE html>\n<html lang="th"><head>\n<meta http-equiv="X-UA-Compatible" content="IE=edge">\n<meta charset="utf-8">\n<title>Othello</title>\n<style>\nhtml,body{margin:0;padding:0}\nbody.tm{font-family:"Segoe UI",Tahoma,Arial,sans-serif;font-size:14px;line-height:1.45}\nbody.dark{background:#1e1f22;color:#e6e6e6}\nbody.light{background:#f4f5f7;color:#1c1e21}\n.wrap{max-width:980px;margin:0 auto;padding:16px}\nh1{font-size:22px;margin:6px 0 14px}\nh2{font-size:17px;margin:4px 0 8px}\na{color:#4c8dff}\n.card{padding:14px;margin:0 0 14px 0;border-radius:8px}\nbody.dark .card{background:#2b2d31;border:1px solid #3d4046}\nbody.light .card{background:#fff;border:1px solid #c9ccd1}\n.row{margin:8px 0}\nlabel{margin-right:14px}\ntextarea,input.txt,select{box-sizing:border-box;font:13px Consolas,"Courier New",monospace;padding:8px;border-radius:6px}\ntextarea{width:100%;min-height:150px;resize:vertical}\nbody.dark textarea,body.dark input.txt,body.dark select{background:#1a1b1e;color:#e6e6e6;border:1px solid #4a4d52}\nbody.light textarea,body.light input.txt,body.light select{background:#fff;color:#1c1e21;border:1px solid #b5b9c0}\ntextarea.bad{border-color:#e5534b !important}\nbutton.btn{font:13px "Segoe UI",Arial,sans-serif;padding:7px 14px;margin:0 6px 6px 0;border-radius:6px;cursor:pointer;border:1px solid #4c8dff;background:#1a66e0;color:#fff}\nbutton.btn.sec{background:transparent;color:inherit;border-color:#7a7f87}\nbutton.btn.on{background:#1a66e0;color:#fff;border-color:#4c8dff}\nbutton.btn:disabled{opacity:.45;cursor:default}\n.msg{min-height:20px;margin-top:6px}\n.err{color:#e5534b}.ok{color:#3fb950}\nbody.light .err{color:#c62828}body.light .ok{color:#1b7f37}\n.drop{border:2px dashed #7a7f87;border-radius:8px;padding:26px;text-align:center}\n.drop.over{border-color:#4c8dff;background:rgba(76,141,255,.12)}\n.preview{max-width:100%;max-height:320px;margin-top:10px;border-radius:6px}\n.small{font-size:12px;opacity:.8}\n.game{display:inline-block;vertical-align:top;width:31%;margin:0 1% 14px 1%;box-sizing:border-box;text-align:center}\n.game svg{width:96px;height:96px}\n.game a.btn{display:inline-block;text-decoration:none;margin-top:8px}\n#cv{width:100%;max-width:800px;display:block;border:1px solid #7a7f87;border-radius:6px;background:#fff}\n.hud{margin:8px 0;font-size:16px}\ntable.oth{border-collapse:collapse;margin:10px auto;background:#2e7d32}\ntable.oth td{width:48px;height:48px;border:1px solid #1b5e20;text-align:center;vertical-align:middle;padding:0;cursor:pointer}\n.disc{width:36px;height:36px;border-radius:50%;margin:0 auto}\n.disc.b{background:#111;border:1px solid #000}\n.disc.w{background:#fff;border:1px solid #999}\n.disc.h{width:10px;height:10px;background:rgba(255,255,255,.5)}\ntable.ttt{border-collapse:collapse;margin:10px auto}\ntable.ttt td{width:90px;height:90px;border:2px solid #7a7f87;text-align:center;font-size:52px;font-weight:bold;cursor:pointer}\n.center{text-align:center}\n</style>\n</head>\n<body class="tm dark">\n<div class="wrap">\n  <a id="back" href="#">&larr; Game Hub</a>\n  <h1>Othello / Reversi</h1>\n  <div class="center">\n    <label>โหมด: <select id="mode"><option value="pvp">2 ผู้เล่น</option><option value="ai">เล่นกับ AI (คุณ = ดำ)</option></select></label>\n    <button id="restart" class="btn" type="button">Restart</button> <button id="muteBtn" class="btn sec" type="button">🔊 เสียง: เปิด</button>\n  </div>\n  <div class="hud center">ดำ ● <b id="cb">2</b> &nbsp; ขาว ○ <b id="cw">2</b></div>\n  <table id="board" class="oth"></table>\n  <div id="status" class="center hud"></div>\n  <div id="stats" class="center small"></div>\n</div>\n<script>\nvar TM = (function () {\n  var api = {};\n  api.$ = function (id) { return document.getElementById(id); };\n\n  api.param = function (name) {\n    var m = new RegExp(\'[?&]\' + name + \'=([^&]*)\').exec(location.search);\n    return m ? decodeURIComponent(m[1]) : null;\n  };\n\n  api.setTheme = function (t) {\n    t = (t === \'light\') ? \'light\' : \'dark\';\n    document.body.className = \'tm \' + t;\n  };\n\n  api.xhr = function (method, url, body, cb) {\n    var x = new XMLHttpRequest();\n    var sep = url.indexOf(\'?\') < 0 ? \'?\' : \'&\';\n    x.open(method, url + sep + \'_=\' + new Date().getTime(), true);  // defeat IE XHR caching\n    x.onreadystatechange = function () {\n      if (x.readyState === 4) { cb(x.status >= 200 && x.status < 300, x.responseText); }\n    };\n    if (body !== null) { x.setRequestHeader(\'Content-Type\', \'application/json\'); }\n    x.send(body);\n  };\n\n  api.pollTheme = function () {\n    function tick() {\n      api.xhr(\'GET\', \'/api/theme\', null, function (ok, txt) {\n        if (ok) { try { api.setTheme(JSON.parse(txt).theme); } catch (e) {} }\n      });\n    }\n    setInterval(tick, 1500);\n  };\n\n  // Persistent store: server-side JSON (Data/GameScores), localStorage only as fallback.\n  api.store = {\n    load: function (key, cb) {\n      api.xhr(\'GET\', \'/api/store/\' + key, null, function (ok, txt) {\n        if (ok) { try { cb(JSON.parse(txt)); return; } catch (e) {} }\n        try { cb(JSON.parse(localStorage.getItem(\'tm_\' + key) || \'{}\')); } catch (e2) { cb({}); }\n      });\n    },\n    save: function (key, obj, cb) {\n      api.xhr(\'POST\', \'/api/store/\' + key, JSON.stringify(obj), function (ok, txt) {\n        if (!ok) { try { localStorage.setItem(\'tm_\' + key, JSON.stringify(obj)); } catch (e) {} }\n        if (cb) { cb(ok); }\n      });\n    }\n  };\n\n  api.copyText = function (text, cb) {\n    function fallback() {\n      var t = document.createElement(\'textarea\');\n      t.value = text; t.style.position = \'fixed\'; t.style.opacity = \'0\';\n      document.body.appendChild(t); t.select();\n      var ok = false;\n      try { ok = document.execCommand(\'copy\'); } catch (e) {}\n      document.body.removeChild(t); cb(ok);\n    }\n    if (window.clipboardData && window.clipboardData.setData) {\n      try { window.clipboardData.setData(\'Text\', text); cb(true); return; } catch (e) {}\n    }\n    if (navigator.clipboard && navigator.clipboard.writeText) {\n      navigator.clipboard.writeText(text).then(function () { cb(true); }, fallback);\n      return;\n    }\n    fallback();\n  };\n\n  api.downloadBytes = function (bytes, name, mime) {\n    var blob;\n    try { blob = new Blob([bytes], { type: mime || \'application/octet-stream\' }); } catch (e) { return false; }\n    if (navigator.msSaveOrOpenBlob) { navigator.msSaveOrOpenBlob(blob, name); return true; }\n    var url = URL.createObjectURL(blob), a = document.createElement(\'a\');\n    a.href = url; a.download = name; document.body.appendChild(a); a.click(); document.body.removeChild(a);\n    setTimeout(function () { URL.revokeObjectURL(url); }, 15000);\n    return true;\n  };\n\n  api.preventFileDrop = function () {\n    function stop(e) { if (e.preventDefault) { e.preventDefault(); } return false; }\n    document.addEventListener(\'dragover\', stop, false);\n    document.addEventListener(\'drop\', stop, false);\n  };\n\n  api.hubLink = function (href) { return href + location.search; };\n\n  api.init = function () {\n    api.setTheme(api.param(\'theme\') || \'dark\');\n    api.pollTheme();\n  };\n  return api;\n})();\n\n(function () {\n  var $ = TM.$, N = 8, board, turn, over, recorded, stats = { black: 0, white: 0, draw: 0 }, busy = false;\n  var DIRS = [[-1, -1], [-1, 0], [-1, 1], [0, -1], [0, 1], [1, -1], [1, 0], [1, 1]];\n  var WT = [[120, -20, 20, 5, 5, 20, -20, 120], [-20, -40, -5, -5, -5, -5, -40, -20], [20, -5, 15, 3, 3, 15, -5, 20],\n    [5, -5, 3, 3, 3, 3, -5, 5], [5, -5, 3, 3, 3, 3, -5, 5], [20, -5, 15, 3, 3, 15, -5, 20],\n    [-20, -40, -5, -5, -5, -5, -40, -20], [120, -20, 20, 5, 5, 20, -20, 120]];\n  TM.init(); TM.preventFileDrop();\n  $(\'back\').href = TM.hubLink(\'game_hub.html\');\n\n  var SFX = (function () {\n    var ctx = null, muted = false, bgmTimer = null, stepIdx = 0;\n    var notes = [220.00, 261.63, 329.63, 392.00, 329.63, 261.63, 246.94, 293.66, 369.99, 440.00, 369.99, 293.66];\n    function ensure() {\n      if (!ctx) {\n        var AC = window.AudioContext || window.webkitAudioContext;\n        if (AC) { try { ctx = new AC(); } catch (e) {} }\n      }\n      if (ctx && ctx.state === \'suspended\') { try { ctx.resume(); } catch (e) {} }\n      return ctx;\n    }\n    function tone(freq, dur, type, vol, slideTo) {\n      if (muted) return;\n      var c = ensure(); if (!c) return;\n      try {\n        var o = c.createOscillator(), g = c.createGain(), now = c.currentTime;\n        o.type = type || \'sine\';\n        o.frequency.setValueAtTime(freq, now);\n        if (slideTo) { o.frequency.exponentialRampToValueAtTime(slideTo, now + dur); }\n        g.gain.setValueAtTime(vol || 0.06, now);\n        g.gain.exponentialRampToValueAtTime(0.0001, now + dur);\n        o.connect(g); g.connect(c.destination);\n        o.start(now); o.stop(now + dur + 0.02);\n      } catch (e) {}\n    }\n    function startBGM() {\n      ensure();\n      if (bgmTimer) return;\n      bgmTimer = setInterval(function () {\n        if (muted || over) return;\n        var f = notes[stepIdx % notes.length];\n        stepIdx++;\n        tone(f, 0.28, \'sine\', 0.025);\n      }, 360);\n    }\n    return {\n      startBGM: startBGM,\n      flip: function (count) {\n        startBGM();\n        var n = Math.min(count || 1, 8), i;\n        tone(300, 0.08, \'triangle\', 0.09, 520);\n        for (i = 0; i < n; i++) {\n          (function (idx) {\n            setTimeout(function () {\n              tone(420 + idx * 55, 0.09, \'sine\', 0.075, 580 + idx * 55);\n            }, (idx + 1) * 45);\n          })(i);\n        }\n      },\n      invalid: function () {\n        startBGM();\n        tone(150, 0.14, \'sawtooth\', 0.06, 110);\n      },\n      toggleMute: function () {\n        muted = !muted;\n        if (!muted) ensure();\n        return muted;\n      }\n    };\n  })();\n\n  $(\'muteBtn\').onclick = function () { var m = SFX.toggleMute(); $(\'muteBtn\').textContent = m ? \'🔇 เสียง: ปิด\' : \'🔊 เสียง: เปิด\'; };\n\n  function newBoard() {\n    var b = [], r, c;\n    for (r = 0; r < N; r++) { b[r] = []; for (c = 0; c < N; c++) { b[r][c] = 0; } }\n    b[3][3] = 2; b[4][4] = 2; b[3][4] = 1; b[4][3] = 1; return b;\n  }\n  function inb(r, c) { return r >= 0 && r < N && c >= 0 && c < N; }\n  function flips(b, r, c, p) {\n    if (b[r][c] !== 0) { return []; }\n    var res = [], d, line, rr, cc;\n    for (d = 0; d < 8; d++) {\n      line = []; rr = r + DIRS[d][0]; cc = c + DIRS[d][1];\n      while (inb(rr, cc) && b[rr][cc] === 3 - p) { line.push([rr, cc]); rr += DIRS[d][0]; cc += DIRS[d][1]; }\n      if (line.length && inb(rr, cc) && b[rr][cc] === p) { res = res.concat(line); }\n    }\n    return res;\n  }\n  function moves(b, p) {\n    var out = [], r, c, f;\n    for (r = 0; r < N; r++) { for (c = 0; c < N; c++) { f = flips(b, r, c, p); if (f.length) { out.push({ r: r, c: c, f: f }); } } }\n    return out;\n  }\n  function play(b, m, p) {\n    var nb = [], r, i;\n    for (r = 0; r < N; r++) { nb[r] = b[r].slice(0); }\n    nb[m.r][m.c] = p;\n    for (i = 0; i < m.f.length; i++) { nb[m.f[i][0]][m.f[i][1]] = p; }\n    return nb;\n  }\n  function count(b) {\n    var x = { 1: 0, 2: 0 }, r, c;\n    for (r = 0; r < N; r++) { for (c = 0; c < N; c++) { if (b[r][c]) { x[b[r][c]]++; } } }\n    return x;\n  }\n  function evalB(b, me) {\n    var s = 0, r, c;\n    for (r = 0; r < N; r++) { for (c = 0; c < N; c++) { if (b[r][c] === me) { s += WT[r][c]; } else if (b[r][c]) { s -= WT[r][c]; } } }\n    return s;\n  }\n  function search(b, p, depth, alpha, beta, me) {\n    var ms = moves(b, p), i, v, best;\n    if (depth === 0) { return evalB(b, me); }\n    if (!ms.length) {\n      if (!moves(b, 3 - p).length) { var cn = count(b); return (cn[me] - cn[3 - me]) * 100; }\n      return search(b, 3 - p, depth - 1, alpha, beta, me);\n    }\n    if (p === me) {\n      best = -1e9;\n      for (i = 0; i < ms.length; i++) { v = search(play(b, ms[i], p), 3 - p, depth - 1, alpha, beta, me); if (v > best) { best = v; } if (best > alpha) { alpha = best; } if (alpha >= beta) { break; } }\n    } else {\n      best = 1e9;\n      for (i = 0; i < ms.length; i++) { v = search(play(b, ms[i], p), 3 - p, depth - 1, alpha, beta, me); if (v < best) { best = v; } if (best < beta) { beta = best; } if (alpha >= beta) { break; } }\n    }\n    return best;\n  }\n  function aiMove(p) {\n    var ms = moves(board, p), best = null, bv = -1e9, i, v;\n    for (i = 0; i < ms.length; i++) { v = search(play(board, ms[i], p), 3 - p, 3, -1e9, 1e9, p); if (v > bv) { bv = v; best = ms[i]; } }\n    return best;\n  }\n\n  function render() {\n    var t = $(\'board\'), r, c, tr, td, d, mv = moves(board, turn), i, hints = {}, cn = count(board);\n    for (i = 0; i < mv.length; i++) { hints[mv[i].r + \',\' + mv[i].c] = mv[i]; }\n    while (t.firstChild) { t.removeChild(t.firstChild); }\n    var tb = document.createElement(\'tbody\'); t.appendChild(tb);\n    for (r = 0; r < N; r++) {\n      tr = document.createElement(\'tr\');\n      for (c = 0; c < N; c++) {\n        td = document.createElement(\'td\');\n        if (board[r][c]) { d = document.createElement(\'div\'); d.className = \'disc \' + (board[r][c] === 1 ? \'b\' : \'w\'); td.appendChild(d); }\n        else if (!over && hints[r + \',\' + c]) { d = document.createElement(\'div\'); d.className = \'disc h\'; td.appendChild(d); }\n        (function (rr, cc) { td.onclick = function () { humanClick(rr, cc); }; })(r, c);\n        tr.appendChild(td);\n      }\n      tb.appendChild(tr);\n    }\n    $(\'cb\').textContent = cn[1]; $(\'cw\').textContent = cn[2];\n  }\n\n  function status(t) { $(\'status\').textContent = t; }\n  function name(p) { return p === 1 ? \'ดำ (Black)\' : \'ขาว (White)\'; }\n\n  function finish() {\n    over = true; render();\n    var cn = count(board), w = cn[1] > cn[2] ? 1 : (cn[2] > cn[1] ? 2 : 0);\n    status(w ? \'จบเกม — \' + name(w) + \' ชนะ \' + cn[1] + \':\' + cn[2] : \'จบเกม — เสมอ \' + cn[1] + \':\' + cn[2]);\n    if (!recorded) {\n      recorded = true;\n      if (w === 1) { stats.black++; } else if (w === 2) { stats.white++; } else { stats.draw++; }\n      TM.store.save(\'othello\', stats); showStats();\n    }\n  }\n  function showStats() { $(\'stats\').textContent = \'สถิติ: ดำชนะ \' + stats.black + \' • ขาวชนะ \' + stats.white + \' • เสมอ \' + stats.draw; }\n\n  function advance() {\n    var next = 3 - turn;\n    if (moves(board, next).length) { turn = next; }\n    else if (moves(board, turn).length) { status(name(next) + \' ไม่มีที่เดิน — ข้ามตา (pass)\'); }\n    else { finish(); return; }\n    render();\n    if (!/ข้ามตา/.test($(\'status\').textContent) || true) { status(\'ตาของ \' + name(turn)); }\n    maybeAI();\n  }\n\n  function maybeAI() {\n    if (over || $(\'mode\').value !== \'ai\' || turn !== 2) { return; }\n    busy = true;\n    setTimeout(function () {\n      var m = aiMove(2);\n      busy = false;\n      if (m) { board = play(board, m, 2); SFX.flip(m.f.length); advance(); }\n    }, 450);\n  }\n\n  function humanClick(r, c) {\n    if (over || busy) { return; }\n    if ($(\'mode\').value === \'ai\' && turn !== 1) { return; }\n    var f = flips(board, r, c, turn);\n    if (!f.length) { SFX.invalid(); status(\'เดินตรงนี้ไม่ได้ (invalid move)\'); return; }\n    board = play(board, { r: r, c: c, f: f }, turn);\n    SFX.flip(f.length);\n    advance();\n  }\n\n  function restart() { board = newBoard(); turn = 1; over = false; recorded = false; busy = false; render(); status(\'ตาของ \' + name(1)); }\n  $(\'restart\').onclick = restart; $(\'mode\').onchange = restart;\n  restart();\n  TM.store.load(\'othello\', function (d) { stats = { black: d.black || 0, white: d.white || 0, draw: d.draw || 0 }; showStats(); });\n})();\n</script>\n</body></html>'
TICTACTOE_HTML = '<!DOCTYPE html>\n<html lang="th"><head>\n<meta http-equiv="X-UA-Compatible" content="IE=edge">\n<meta charset="utf-8">\n<title>Tic-Tac-Toe</title>\n<style>\nhtml,body{margin:0;padding:0}\nbody.tm{font-family:"Segoe UI",Tahoma,Arial,sans-serif;font-size:14px;line-height:1.45}\nbody.dark{background:#1e1f22;color:#e6e6e6}\nbody.light{background:#f4f5f7;color:#1c1e21}\n.wrap{max-width:980px;margin:0 auto;padding:16px}\nh1{font-size:22px;margin:6px 0 14px}\nh2{font-size:17px;margin:4px 0 8px}\na{color:#4c8dff}\n.card{padding:14px;margin:0 0 14px 0;border-radius:8px}\nbody.dark .card{background:#2b2d31;border:1px solid #3d4046}\nbody.light .card{background:#fff;border:1px solid #c9ccd1}\n.row{margin:8px 0}\nlabel{margin-right:14px}\ntextarea,input.txt,select{box-sizing:border-box;font:13px Consolas,"Courier New",monospace;padding:8px;border-radius:6px}\ntextarea{width:100%;min-height:150px;resize:vertical}\nbody.dark textarea,body.dark input.txt,body.dark select{background:#1a1b1e;color:#e6e6e6;border:1px solid #4a4d52}\nbody.light textarea,body.light input.txt,body.light select{background:#fff;color:#1c1e21;border:1px solid #b5b9c0}\ntextarea.bad{border-color:#e5534b !important}\nbutton.btn{font:13px "Segoe UI",Arial,sans-serif;padding:7px 14px;margin:0 6px 6px 0;border-radius:6px;cursor:pointer;border:1px solid #4c8dff;background:#1a66e0;color:#fff}\nbutton.btn.sec{background:transparent;color:inherit;border-color:#7a7f87}\nbutton.btn.on{background:#1a66e0;color:#fff;border-color:#4c8dff}\nbutton.btn:disabled{opacity:.45;cursor:default}\n.msg{min-height:20px;margin-top:6px}\n.err{color:#e5534b}.ok{color:#3fb950}\nbody.light .err{color:#c62828}body.light .ok{color:#1b7f37}\n.drop{border:2px dashed #7a7f87;border-radius:8px;padding:26px;text-align:center}\n.drop.over{border-color:#4c8dff;background:rgba(76,141,255,.12)}\n.preview{max-width:100%;max-height:320px;margin-top:10px;border-radius:6px}\n.small{font-size:12px;opacity:.8}\n.game{display:inline-block;vertical-align:top;width:31%;margin:0 1% 14px 1%;box-sizing:border-box;text-align:center}\n.game svg{width:96px;height:96px}\n.game a.btn{display:inline-block;text-decoration:none;margin-top:8px}\n#cv{width:100%;max-width:800px;display:block;border:1px solid #7a7f87;border-radius:6px;background:#fff}\n.hud{margin:8px 0;font-size:16px}\ntable.oth{border-collapse:collapse;margin:10px auto;background:#2e7d32}\ntable.oth td{width:48px;height:48px;border:1px solid #1b5e20;text-align:center;vertical-align:middle;padding:0;cursor:pointer}\n.disc{width:36px;height:36px;border-radius:50%;margin:0 auto}\n.disc.b{background:#111;border:1px solid #000}\n.disc.w{background:#fff;border:1px solid #999}\n.disc.h{width:10px;height:10px;background:rgba(255,255,255,.5)}\ntable.ttt{border-collapse:collapse;margin:10px auto}\ntable.ttt td{width:90px;height:90px;border:2px solid #7a7f87;text-align:center;font-size:52px;font-weight:bold;cursor:pointer}\n.center{text-align:center}\n</style>\n</head>\n<body class="tm dark">\n<div class="wrap">\n  <a id="back" href="#">&larr; Game Hub</a>\n  <h1>Tic-Tac-Toe (OX)</h1>\n  <div class="center">\n    <label>โหมด: <select id="mode"><option value="pvp">2 ผู้เล่น</option><option value="ai">เล่นกับ AI (คุณ = X)</option></select></label>\n    <button id="restart" class="btn" type="button">Restart</button> <button id="muteBtn" class="btn sec" type="button">🔊 เสียง: เปิด</button>\n  </div>\n  <table id="board" class="ttt"></table>\n  <div id="status" class="center hud"></div>\n  <div id="stats" class="center small"></div>\n</div>\n<script>\nvar TM = (function () {\n  var api = {};\n  api.$ = function (id) { return document.getElementById(id); };\n\n  api.param = function (name) {\n    var m = new RegExp(\'[?&]\' + name + \'=([^&]*)\').exec(location.search);\n    return m ? decodeURIComponent(m[1]) : null;\n  };\n\n  api.setTheme = function (t) {\n    t = (t === \'light\') ? \'light\' : \'dark\';\n    document.body.className = \'tm \' + t;\n  };\n\n  api.xhr = function (method, url, body, cb) {\n    var x = new XMLHttpRequest();\n    var sep = url.indexOf(\'?\') < 0 ? \'?\' : \'&\';\n    x.open(method, url + sep + \'_=\' + new Date().getTime(), true);  // defeat IE XHR caching\n    x.onreadystatechange = function () {\n      if (x.readyState === 4) { cb(x.status >= 200 && x.status < 300, x.responseText); }\n    };\n    if (body !== null) { x.setRequestHeader(\'Content-Type\', \'application/json\'); }\n    x.send(body);\n  };\n\n  api.pollTheme = function () {\n    function tick() {\n      api.xhr(\'GET\', \'/api/theme\', null, function (ok, txt) {\n        if (ok) { try { api.setTheme(JSON.parse(txt).theme); } catch (e) {} }\n      });\n    }\n    setInterval(tick, 1500);\n  };\n\n  // Persistent store: server-side JSON (Data/GameScores), localStorage only as fallback.\n  api.store = {\n    load: function (key, cb) {\n      api.xhr(\'GET\', \'/api/store/\' + key, null, function (ok, txt) {\n        if (ok) { try { cb(JSON.parse(txt)); return; } catch (e) {} }\n        try { cb(JSON.parse(localStorage.getItem(\'tm_\' + key) || \'{}\')); } catch (e2) { cb({}); }\n      });\n    },\n    save: function (key, obj, cb) {\n      api.xhr(\'POST\', \'/api/store/\' + key, JSON.stringify(obj), function (ok, txt) {\n        if (!ok) { try { localStorage.setItem(\'tm_\' + key, JSON.stringify(obj)); } catch (e) {} }\n        if (cb) { cb(ok); }\n      });\n    }\n  };\n\n  api.copyText = function (text, cb) {\n    function fallback() {\n      var t = document.createElement(\'textarea\');\n      t.value = text; t.style.position = \'fixed\'; t.style.opacity = \'0\';\n      document.body.appendChild(t); t.select();\n      var ok = false;\n      try { ok = document.execCommand(\'copy\'); } catch (e) {}\n      document.body.removeChild(t); cb(ok);\n    }\n    if (window.clipboardData && window.clipboardData.setData) {\n      try { window.clipboardData.setData(\'Text\', text); cb(true); return; } catch (e) {}\n    }\n    if (navigator.clipboard && navigator.clipboard.writeText) {\n      navigator.clipboard.writeText(text).then(function () { cb(true); }, fallback);\n      return;\n    }\n    fallback();\n  };\n\n  api.downloadBytes = function (bytes, name, mime) {\n    var blob;\n    try { blob = new Blob([bytes], { type: mime || \'application/octet-stream\' }); } catch (e) { return false; }\n    if (navigator.msSaveOrOpenBlob) { navigator.msSaveOrOpenBlob(blob, name); return true; }\n    var url = URL.createObjectURL(blob), a = document.createElement(\'a\');\n    a.href = url; a.download = name; document.body.appendChild(a); a.click(); document.body.removeChild(a);\n    setTimeout(function () { URL.revokeObjectURL(url); }, 15000);\n    return true;\n  };\n\n  api.preventFileDrop = function () {\n    function stop(e) { if (e.preventDefault) { e.preventDefault(); } return false; }\n    document.addEventListener(\'dragover\', stop, false);\n    document.addEventListener(\'drop\', stop, false);\n  };\n\n  api.hubLink = function (href) { return href + location.search; };\n\n  api.init = function () {\n    api.setTheme(api.param(\'theme\') || \'dark\');\n    api.pollTheme();\n  };\n  return api;\n})();\n\n\n(function () {\n  var $ = TM.$, b, turn, over, stats = { x: 0, o: 0, draw: 0 };\n  var LINES = [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [0, 4, 8], [2, 4, 6]];\n  TM.init(); TM.preventFileDrop();\n  $(\'back\').href = TM.hubLink(\'game_hub.html\');\n\n  var SFX = (function () {\n    var ctx = null, muted = false, bgmTimer = null, stepIdx = 0;\n    var notes = [329.63, 392.00, 440.00, 523.25, 440.00, 392.00, 293.66, 349.23, 392.00, 493.88, 392.00, 349.23];\n    function ensure() {\n      if (!ctx) {\n        var AC = window.AudioContext || window.webkitAudioContext;\n        if (AC) { try { ctx = new AC(); } catch (e) {} }\n      }\n      if (ctx && ctx.state === \'suspended\') { try { ctx.resume(); } catch (e) {} }\n      return ctx;\n    }\n    function tone(freq, dur, type, vol, slideTo) {\n      if (muted) return;\n      var c = ensure(); if (!c) return;\n      try {\n        var o = c.createOscillator(), g = c.createGain(), now = c.currentTime;\n        o.type = type || \'triangle\';\n        o.frequency.setValueAtTime(freq, now);\n        if (slideTo) { o.frequency.exponentialRampToValueAtTime(slideTo, now + dur); }\n        g.gain.setValueAtTime(vol || 0.07, now);\n        g.gain.exponentialRampToValueAtTime(0.0001, now + dur);\n        o.connect(g); g.connect(c.destination);\n        o.start(now); o.stop(now + dur + 0.02);\n      } catch (e) {}\n    }\n    function startBGM() {\n      ensure();\n      if (bgmTimer) return;\n      bgmTimer = setInterval(function () {\n        if (muted || over) return;\n        var f = notes[stepIdx % notes.length];\n        stepIdx++;\n        tone(f, 0.22, \'sine\', 0.025);\n      }, 280);\n    }\n    return {\n      startBGM: startBGM,\n      move: function (mark) {\n        startBGM();\n        if (mark === \'X\') {\n          tone(520, 0.10, \'triangle\', 0.09, 760);\n        } else {\n          tone(420, 0.12, \'sine\', 0.09, 300);\n        }\n      },\n      win: function () {\n        var ch = [523.25, 659.25, 783.99, 1046.50], i;\n        for (i = 0; i < ch.length; i++) {\n          (function (idx) {\n            setTimeout(function () { tone(ch[idx], 0.16, \'triangle\', 0.10); }, idx * 90);\n          })(i);\n        }\n      },\n      draw: function () {\n        tone(330, 0.15, \'sine\', 0.08, 220);\n      },\n      toggleMute: function () {\n        muted = !muted;\n        if (!muted) ensure();\n        return muted;\n      }\n    };\n  })();\n\n  $(\'muteBtn\').onclick = function () { var m = SFX.toggleMute(); $(\'muteBtn\').textContent = m ? \'🔇 เสียง: ปิด\' : \'🔊 เสียง: เปิด\'; };\n\n  function winner(s) {\n    var i, l;\n    for (i = 0; i < LINES.length; i++) { l = LINES[i]; if (s[l[0]] && s[l[0]] === s[l[1]] && s[l[0]] === s[l[2]]) { return s[l[0]]; } }\n    return s.join(\'\').length === 9 ? \'draw\' : null;\n  }\n  function minimax(s, p, depth) {\n    var w = winner(s), i, v, best;\n    if (w === \'O\') { return 10 - depth; } if (w === \'X\') { return depth - 10; } if (w === \'draw\') { return 0; }\n    best = p === \'O\' ? -100 : 100;\n    for (i = 0; i < 9; i++) {\n      if (!s[i]) {\n        s[i] = p; v = minimax(s, p === \'O\' ? \'X\' : \'O\', depth + 1); s[i] = \'\';\n        if (p === \'O\' ? v > best : v < best) { best = v; }\n      }\n    }\n    return best;\n  }\n  function aiMove() {\n    var i, v, best = -100, mv = -1;\n    for (i = 0; i < 9; i++) { if (!b[i]) { b[i] = \'O\'; v = minimax(b, \'X\', 1); b[i] = \'\'; if (v > best) { best = v; mv = i; } } }\n    return mv;\n  }\n  function status(t) { $(\'status\').textContent = t; }\n  function render() {\n    var t = $(\'board\'), r, c, tr, td, tb = document.createElement(\'tbody\');\n    while (t.firstChild) { t.removeChild(t.firstChild); }\n    t.appendChild(tb);\n    for (r = 0; r < 3; r++) {\n      tr = document.createElement(\'tr\');\n      for (c = 0; c < 3; c++) {\n        td = document.createElement(\'td\'); td.textContent = b[r * 3 + c];\n        td.style.color = b[r * 3 + c] === \'X\' ? \'#4c8dff\' : \'#e5534b\';\n        (function (i) { td.onclick = function () { click(i); }; })(r * 3 + c);\n        tr.appendChild(td);\n      }\n      tb.appendChild(tr);\n    }\n  }\n  function check() {\n    var w = winner(b);\n    if (!w) { return false; }\n    over = true;\n    if (w === \'draw\') { stats.draw++; status(\'เสมอ (Draw)\'); SFX.draw(); } else { stats[w.toLowerCase()]++; status(\'ผู้ชนะ: \' + w); SFX.win(); }\n    TM.store.save(\'tictactoe\', stats); showStats(); return true;\n  }\n  function showStats() { $(\'stats\').textContent = \'สถิติ: X ชนะ \' + stats.x + \' • O ชนะ \' + stats.o + \' • เสมอ \' + stats.draw; }\n  function click(i) {\n    if (over || b[i]) { return; }\n    if ($(\'mode\').value === \'ai\' && turn !== \'X\') { return; }\n    b[i] = turn; SFX.move(turn); render();\n    if (check()) { return; }\n    turn = turn === \'X\' ? \'O\' : \'X\'; status(\'ตาของ \' + turn);\n    if ($(\'mode\').value === \'ai\' && turn === \'O\') {\n      setTimeout(function () {\n        var m = aiMove(); if (m >= 0) { b[m] = \'O\'; SFX.move(\'O\'); render(); if (check()) { return; } turn = \'X\'; status(\'ตาของ X\'); }\n      }, 300);\n    }\n  }\n  function restart() { b = [\'\', \'\', \'\', \'\', \'\', \'\', \'\', \'\', \'\']; turn = \'X\'; over = false; render(); status(\'ตาของ X\'); }\n  $(\'restart\').onclick = restart; $(\'mode\').onchange = restart;\n  restart();\n  TM.store.load(\'tictactoe\', function (d) { stats = { x: d.x || 0, o: d.o || 0, draw: d.draw || 0 }; showStats(); });\n})();\n</script>\n</body></html>'
STELLAR_HTML = '<!DOCTYPE html>\n<html lang="th">\n<head>\n<meta charset="UTF-8">\n<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no, viewport-fit=cover">\n<title>STELLAR RAID // 2026 HD REMASTER</title>\n<style>\n  :root{ --accent:#4ef0ff; }\n  *{box-sizing:border-box; -webkit-tap-highlight-color: transparent; user-select:none;}\n  html,body{margin:0;padding:0;width:100%;height:100%;background:#000;overflow:hidden;\n    font-family:\'Segoe UI\',Tahoma,\'Noto Sans Thai\',sans-serif; touch-action:none;}\n  #app{position:fixed;inset:0;display:flex;align-items:center;justify-content:center;background:#000;}\n  #game{image-rendering:pixelated;image-rendering:crisp-edges;background:#000;display:block;}\n  #uiOverlay{position:fixed;inset:0;pointer-events:none;color:#eafcff;}\n  #hudTop{position:absolute;top:0;left:0;right:0;display:flex;justify-content:space-between;\n    padding:6px 12px;padding-top:max(6px, env(safe-area-inset-top));\n    font-size:clamp(11px,1.6vw,16px);letter-spacing:1px;text-shadow:0 0 6px #000,0 0 2px #000;}\n  #hudTop div span{color:var(--accent);font-weight:bold;}\n  #meterRow{position:absolute;bottom:0;left:0;right:0;display:flex;align-items:flex-end;justify-content:center;\n    gap:4px;padding:6px;padding-bottom:max(6px, env(safe-area-inset-bottom));}\n  .mSeg{width:clamp(26px,5vw,42px);height:clamp(18px,3.2vw,26px);border:1px solid #3a6;\n    background:rgba(10,20,30,.55);display:flex;align-items:center;justify-content:center;\n    font-size:clamp(8px,1.3vw,11px);color:#7fd; border-radius:3px;}\n  .mSeg.active{background:var(--accent);color:#001;border-color:#fff;box-shadow:0 0 10px var(--accent);}\n  #weaponTag{position:absolute;bottom:34px;left:50%;transform:translateX(-50%);\n    font-size:clamp(9px,1.5vw,13px);color:#ffe27a;text-shadow:0 0 6px #000;white-space:nowrap;}\n  #bossBarWrap{position:absolute;top:30px;left:50%;transform:translateX(-50%);width:min(70vw,420px);\n    text-align:center;}\n  #bossBarWrap.hidden{display:none;}\n  #bossNameTag{font-size:clamp(10px,1.6vw,14px);color:#ff6b6b;text-shadow:0 0 6px #000;margin-bottom:2px;}\n  #bossBarOuter{height:10px;border:1px solid #ff6b6b;background:rgba(40,0,0,.5);border-radius:4px;overflow:hidden;}\n  #bossBarFill{height:100%;background:linear-gradient(90deg,#ff2d2d,#ff9b6b);width:100%;}\n\n  .screen{position:fixed;inset:0;display:flex;flex-direction:column;align-items:center;justify-content:center;\n    background:radial-gradient(ellipse at center,rgba(5,10,30,.92),rgba(0,0,5,.97));\n    color:#eafcff;text-align:center;padding:20px;gap:14px;z-index:20;}\n  .hidden{display:none !important;}\n  .logo{font-size:clamp(26px,6vw,56px);font-weight:900;letter-spacing:4px;color:var(--accent);\n    text-shadow:0 0 18px var(--accent),0 0 40px #0af;}\n  .subtitle{font-size:clamp(12px,2.2vw,18px);color:#9fe; letter-spacing:2px;margin-top:-10px;}\n  .panel{background:rgba(10,18,36,.7);border:1px solid #2a5;border-radius:10px;padding:16px 20px;\n    max-width:560px;width:90%;}\n  .btn{pointer-events:auto;cursor:pointer;background:linear-gradient(180deg,#1b3a52,#0c1b2b);\n    color:#eafcff;border:1px solid var(--accent);padding:12px 28px;border-radius:8px;\n    font-size:clamp(14px,2.2vw,18px);letter-spacing:1px;transition:.15s;}\n  .btn:active{transform:scale(.95);background:var(--accent);color:#012;}\n  .btn:disabled{opacity:.35;cursor:not-allowed;}\n  .screen h2{margin:0;font-size:clamp(18px,3vw,30px);color:var(--accent);letter-spacing:2px;}\n  .screen p{margin:4px 0;font-size:clamp(11px,1.8vw,15px);line-height:1.6;color:#cdf;}\n  .row{display:flex;gap:10px;flex-wrap:wrap;justify-content:center;}\n\n  #shopList{display:flex;flex-direction:column;gap:8px;max-height:46vh;overflow-y:auto;width:100%;}\n  .shopItem{display:grid;grid-template-columns:1fr auto;align-items:center;gap:6px;\n    background:rgba(20,40,60,.6);border:1px solid #275;border-radius:8px;padding:8px 12px;}\n  .siName{font-weight:bold;color:#ffe27a;font-size:clamp(12px,2vw,15px);}\n  .siDesc{font-size:clamp(10px,1.6vw,12px);color:#aef;grid-column:1;}\n  .siCost{font-size:clamp(10px,1.6vw,12px);color:#9fe;grid-column:1;}\n  .shopItem button{grid-row:1/3;grid-column:2;pointer-events:auto;cursor:pointer;background:#123;\n    color:#fff;border:1px solid var(--accent);border-radius:6px;padding:8px 14px;font-size:clamp(11px,1.8vw,14px);}\n  .shopItem button:disabled{opacity:.3;}\n\n  #meterLegend{font-size:clamp(9px,1.4vw,11px);color:#8ad;max-width:520px;}\n\n  /* touch controls */\n  #touchControls{position:fixed;inset:0;pointer-events:none;z-index:15;display:none;}\n  body.has-touch #touchControls{display:block;}\n  #joyBase{position:absolute;left:max(18px, env(safe-area-inset-left));bottom:max(18px, env(safe-area-inset-bottom));\n    width:clamp(90px,22vw,130px);height:clamp(90px,22vw,130px);border-radius:50%;\n    background:rgba(60,200,255,.12);border:2px solid rgba(120,220,255,.4);pointer-events:auto;touch-action:none;}\n  #joyStick{position:absolute;left:50%;top:50%;width:46%;height:46%;margin-left:-23%;margin-top:-23%;\n    border-radius:50%;background:rgba(120,230,255,.55);border:2px solid #fff;}\n  .tbtn{position:absolute;pointer-events:auto;border-radius:50%;display:flex;align-items:center;justify-content:center;\n    font-weight:bold;color:#eafcff;background:rgba(255,120,120,.18);border:2px solid rgba(255,160,160,.55);\n    touch-action:none;letter-spacing:1px;}\n  #btnFire{right:max(26px, env(safe-area-inset-right));bottom:max(60px, env(safe-area-inset-bottom));\n    width:clamp(74px,16vw,96px);height:clamp(74px,16vw,96px);font-size:clamp(12px,2vw,15px);\n    background:rgba(255,100,100,.22);}\n  #btnPower{right:max(110px, calc(env(safe-area-inset-right) + 90px));bottom:max(150px, calc(env(safe-area-inset-bottom) + 90px));\n    width:clamp(56px,13vw,74px);height:clamp(56px,13vw,74px);font-size:clamp(10px,1.7vw,13px);\n    background:rgba(255,220,100,.2);border-color:rgba(255,230,140,.6);}\n  #btnPause{right:max(14px, env(safe-area-inset-right));top:max(14px, env(safe-area-inset-top));\n    width:38px;height:38px;font-size:16px;background:rgba(160,160,255,.2);}\n\n  #rotateHint{position:fixed;inset:0;z-index:999;background:#000;color:#9fe;display:none;\n    align-items:center;justify-content:center;text-align:center;font-size:clamp(14px,4vw,20px);padding:20px;}\n  @media (orientation:portrait) and (max-width:900px){\n    #rotateHint{display:flex;}\n    #app{display:none;}\n  }\n  ::-webkit-scrollbar{width:6px;} ::-webkit-scrollbar-thumb{background:#2a5;border-radius:4px;}\n  .hl{display:flex;align-items:center;gap:14px;}\n  #hpBar{display:flex;align-items:center;gap:3px;color:#7dffa0;font-weight:bold;}\n  #hpBar b{display:inline-block;width:clamp(16px,3.2vw,28px);height:clamp(8px,1.5vw,13px);border:1px solid #cfe;background:rgba(60,10,25,.7);transform:skewX(-20deg);}\n  #hpBar b.on{background:linear-gradient(#a6ffc0,#17b85a);box-shadow:0 0 8px #3f9;}\n  #hpBar.low b.on{background:linear-gradient(#ff9a9a,#e02020);box-shadow:0 0 8px #f44;animation:hpb .5s infinite alternate;}\n  @keyframes hpb{to{opacity:.4}}\n</style>\n</head>\n<body>\n\n<div id="rotateHint">🔄 กรุณาหมุนอุปกรณ์เป็นแนวนอน (Landscape)<br>เพื่อประสบการณ์เกมที่ดีที่สุด</div>\n\n<div id="app">\n  <canvas id="game"></canvas>\n\n  <div id="uiOverlay">\n    <div id="hudTop">\n      <div class="hl"><div>SCORE <span id="hudScore">0</span></div><div id="hpBar">HP <b></b><b></b><b></b></div></div>\n      <div>STAGE <span id="hudStage">1/8</span></div>\n      <div>♥ <span id="hudLives">5</span></div><div>CONT <span id="hudContinues">2</span></div>\n      <div>💎 <span id="hudCrystals">0</span></div>\n    </div>\n    <div id="bossBarWrap" class="hidden">\n      <div id="bossNameTag">BOSS</div>\n      <div id="bossBarOuter"><div id="bossBarFill"></div></div>\n    </div>\n    <div id="weaponTag">NORMAL</div>\n    <div id="meterRow">\n      <div class="mSeg" id="m0">SPD</div>\n      <div class="mSeg" id="m1">MIS</div>\n      <div class="mSeg" id="m2">DBL</div>\n      <div class="mSeg" id="m3">LAS</div>\n      <div class="mSeg" id="m4">RIP</div>\n      <div class="mSeg" id="m5">OPT</div>\n      <div class="mSeg" id="m6">BAR</div>\n    </div>\n  </div>\n\n  <!-- TITLE -->\n  <div id="screenTitle" class="screen">\n    <div class="logo">STELLAR RAID</div>\n    <div class="subtitle">PIXEL ART HD REMASTER — 2026 EDITION</div>\n    <div class="panel">\n      <p>ขับยานรบข้ามอวกาศ 8 ด่าน เก็บแคปซูลพลังเพื่ออัปเกรด SPEED / MISSILE / DOUBLE / LASER / RIPPLE / OPTION / BARRIER\n      เก็บคริสตัลไปซื้อของในร้านค้าระหว่างด่าน แล้วปราบบอสทั้งหมดเพื่อกอบกู้กาแล็กซี!</p>\n      <p style="color:#8ad">PC: ลูกศร/WASD เคลื่อนที่ · Z/Space ยิง · X ใช้พลัง · P หยุดชั่วคราว<br>\n      Mobile/Tablet: จอยสติ๊กซ้ายล่างเคลื่อนที่ · ปุ่ม FIRE ยิง · ปุ่ม POWER ใช้พลัง</p>\n    </div>\n    <div class="row"><button class="btn" id="startBtn">▶ เริ่มเกม</button></div>\n  </div>\n\n  <!-- BRIEFING -->\n  <div id="screenBriefing" class="screen hidden">\n    <h2 id="briefStageNum">STAGE 1</h2>\n    <div class="logo" style="font-size:clamp(20px,4vw,34px)" id="briefStageName">—</div>\n    <div class="panel">\n      <p id="briefBossName">เป้าหมาย: —</p>\n      <p>เตรียมอาวุธให้พร้อม แล้วลุยเข้าสู่สนามรบ!</p>\n    </div>\n    <div class="row"><button class="btn" id="startStageBtn">🚀 เริ่มด่าน</button></div>\n  </div>\n\n  <!-- SHOP -->\n  <div id="screenShop" class="screen hidden">\n    <h2>🛒 ร้านค้าประจำกองยาน</h2>\n    <div class="panel">\n      <p>คริสตัลคงเหลือ: <span id="shopCrystals" style="color:#ffe27a">0</span> 💎</p>\n      <div id="shopList"></div>\n    </div>\n    <div class="row"><button class="btn" id="shopContinueBtn">ไปด่านต่อไป ▶</button></div>\n  </div>\n\n  <!-- STAGE CLEAR (auto only, no buttons) -->\n  <div id="screenStageClear" class="screen hidden">\n    <div class="logo" style="color:#ffe27a;text-shadow:0 0 18px #ffe27a">STAGE CLEAR!</div>\n    <p id="stageClearText">กำลังเดินทางสู่ร้านค้า...</p>\n  </div>\n\n  <!-- GAME OVER -->\n  <div id="screenGameOver" class="screen hidden">\n    <div class="logo" style="color:#ff5050;text-shadow:0 0 18px #ff5050">GAME OVER</div>\n    <div class="panel"><p>คะแนนสุดท้าย: <span id="goScore" style="color:#ffe27a">0</span></p></div>\n    <div class="row">\n      <button class="btn" id="continueBtn">▶ Continue (2)</button>\n      <button class="btn" id="retryBtn">🔁 เล่นใหม่</button>\n    </div>\n  </div>\n\n  <!-- ENDING -->\n  <div id="screenEnding" class="screen hidden">\n    <div class="logo">MISSION COMPLETE</div>\n    <div class="panel">\n      <p>ยานรบ Nova Blitz !!! เจ้าได้ทำลายแกนเอไอ "ซิงกูลาริตี้" และปลดปล่อยกาแล็กซีจากกองทัพเครื่องจักรแล้ว\n      ชื่อของเจ้าจะถูกจารึกไว้ในประวัติศาสตร์แห่งห้วงอวกาศตลอดกาล</p>\n      <p>คะแนนรวม: <span id="endScore" style="color:#ffe27a">0</span> &nbsp;|&nbsp; คริสตัลที่เก็บได้: <span id="endCrystals" style="color:#9fe">0</span></p>\n      <p style="color:#8ad">— ขอบคุณที่เล่น STELLAR RAID : 2026 HD REMASTER —</p>\n    </div>\n    <div class="row"><button class="btn" id="endMenuBtn">กลับสู่เมนูหลัก</button></div>\n  </div>\n\n  <!-- PAUSE -->\n  <div id="screenPause" class="screen hidden">\n    <h2>⏸ หยุดชั่วคราว</h2>\n    <div class="row">\n      <button class="btn" id="resumeBtn">เล่นต่อ</button>\n      <button class="btn" id="quitBtn">กลับเมนูหลัก</button>\n    </div>\n  </div>\n\n  <div id="touchControls">\n    <div id="joyBase"><div id="joyStick"></div></div>\n    <div class="tbtn" id="btnFire">FIRE</div>\n    <div class="tbtn" id="btnPower">POWER</div>\n    <div class="tbtn" id="btnPause">⏸</div>\n  </div>\n</div>\n\n<script>\n(function(){\n"use strict";\n/* ---------- basic setup ---------- */\nconst BASE_W=384, BASE_H=216;\nconst canvas=document.getElementById(\'game\');\nconst ctx=canvas.getContext(\'2d\');\nctx.imageSmoothingEnabled=false;\ncanvas.width=BASE_W*2; canvas.height=BASE_H*2;\nfunction resize(){\n  const scale=Math.min(window.innerWidth/BASE_W, window.innerHeight/BASE_H);\n  canvas.style.width=Math.floor(BASE_W*scale)+\'px\';\n  canvas.style.height=Math.floor(BASE_H*scale)+\'px\';\n}\nwindow.addEventListener(\'resize\',resize); resize();\nif(\'ontouchstart\' in window || navigator.maxTouchPoints>0) document.body.classList.add(\'has-touch\');\n\nfunction rand(a,b){return a+Math.random()*(b-a);}\nfunction clamp(v,a,b){return Math.max(a,Math.min(b,v));}\nfunction rectHit(a,b){return a.x-a.w/2<b.x+b.w/2 && a.x+a.w/2>b.x-b.w/2 && a.y-a.h/2<b.y+b.h/2 && a.y+a.h/2>b.y-b.h/2;}\n\n/* ---------- audio ---------- */\nlet audioCtx=null;\nfunction ensureAudio(){ if(!audioCtx){ try{ audioCtx=new (window.AudioContext||window.webkitAudioContext)(); }catch(e){} } }\nfunction playTone(freq,dur,type,vol){\n  if(!audioCtx) return;\n  try{\n    const o=audioCtx.createOscillator(), g=audioCtx.createGain();\n    o.type=type||\'square\'; o.frequency.value=freq; g.gain.value=vol||0.07;\n    o.connect(g); g.connect(audioCtx.destination);\n    o.start();\n    g.gain.exponentialRampToValueAtTime(0.0001, audioCtx.currentTime+dur);\n    o.stop(audioCtx.currentTime+dur+0.02);\n  }catch(e){}\n}\n\n/* ---------- input ---------- */\nconst keys={};\nwindow.addEventListener(\'keydown\',e=>{\n  keys[e.code]=true;\n  if([\'Space\',\'ArrowUp\',\'ArrowDown\',\'ArrowLeft\',\'ArrowRight\'].includes(e.code)) e.preventDefault();\n  if(e.code===\'KeyX\' && !e.repeat) activatePower();\n  if(e.code===\'KeyP\' && !e.repeat) togglePause();\n});\nwindow.addEventListener(\'keyup\',e=>{keys[e.code]=false;});\n\nlet fireHeld=false;\nconst joy={active:false,x:0,y:0};\nconst joyBase=document.getElementById(\'joyBase\'), joyStick=document.getElementById(\'joyStick\');\nlet joyPid=null;\nfunction joyStart(e){ joyPid=e.pointerId; try{joyBase.setPointerCapture(joyPid);}catch(er){} joy.active=true; updateJoy(e); e.preventDefault(); }\nfunction updateJoy(e){\n  const r=joyBase.getBoundingClientRect();\n  const cx=r.left+r.width/2, cy=r.top+r.height/2;\n  let dx=e.clientX-cx, dy=e.clientY-cy;\n  const rad=r.width/2, len=Math.hypot(dx,dy);\n  if(len>rad){dx=dx/len*rad; dy=dy/len*rad;}\n  joy.x=dx/rad; joy.y=dy/rad;\n  joyStick.style.transform=`translate(${dx}px,${dy}px)`;\n}\nfunction joyEnd(e){ if(e.pointerId!==joyPid) return; joy.active=false; joy.x=0; joy.y=0; joyStick.style.transform=\'translate(0,0)\'; joyPid=null; }\njoyBase.addEventListener(\'pointerdown\',joyStart);\njoyBase.addEventListener(\'pointermove\',e=>{ if(joy.active && e.pointerId===joyPid) updateJoy(e); });\nwindow.addEventListener(\'pointerup\',joyEnd);\nwindow.addEventListener(\'pointercancel\',joyEnd);\n\nconst btnFire=document.getElementById(\'btnFire\');\nbtnFire.addEventListener(\'pointerdown\',e=>{ ensureAudio(); fireHeld=true; e.preventDefault(); });\nbtnFire.addEventListener(\'pointerup\',()=>fireHeld=false);\nbtnFire.addEventListener(\'pointercancel\',()=>fireHeld=false);\ndocument.getElementById(\'btnPower\').addEventListener(\'pointerdown\',e=>{ e.preventDefault(); activatePower(); });\ndocument.getElementById(\'btnPause\').addEventListener(\'pointerdown\',e=>{ e.preventDefault(); togglePause(); });\n\nfunction getMoveVector(){\n  let x=0,y=0;\n  if(keys[\'ArrowLeft\']||keys[\'KeyA\']) x-=1;\n  if(keys[\'ArrowRight\']||keys[\'KeyD\']) x+=1;\n  if(keys[\'ArrowUp\']||keys[\'KeyW\']) y-=1;\n  if(keys[\'ArrowDown\']||keys[\'KeyS\']) y+=1;\n  if(joy.active){ x+=joy.x; y+=joy.y; }\n  const len=Math.hypot(x,y);\n  if(len>1){x/=len;y/=len;}\n  return {x,y};\n}\nfunction isFiring(){ return !!(keys[\'Space\']||keys[\'KeyZ\']||fireHeld); }\n\n/* ---------- content data ---------- */\nconst STAGE_COLORS=[\n {sky1:\'#050819\',sky2:\'#0b1540\',accent:\'#4ef0ff\',name:\'เนบิวลาประตูดาว\'},\n {sky1:\'#1a0505\',sky2:\'#3a0d0d\',accent:\'#ff7a33\',name:\'ภูเขาไฟคริมสัน\'},\n {sky1:\'#04131a\',sky2:\'#07314a\',accent:\'#7fe8ff\',name:\'ห้วงน้ำแข็งนิรันดร์\'},\n {sky1:\'#141414\',sky2:\'#2b2b33\',accent:\'#ffd84d\',name:\'โรงงานเมกะฟอร์จ\'},\n {sky1:\'#0a1a0a\',sky2:\'#1f3a1a\',accent:\'#9bff6a\',name:\'รังชีวะไบโอไฮฟ์\'},\n {sky1:\'#0c0318\',sky2:\'#260843\',accent:\'#c77dff\',name:\'รอยแยกห้วงว่าง\'},\n {sky1:\'#050505\',sky2:\'#1a1a2e\',accent:\'#ff4d6d\',name:\'ป้อมปราการวงโคจร\'},\n {sky1:\'#000000\',sky2:\'#1a0030\',accent:\'#ffffff\',name:\'แกนกำเนิดภาวะเอกฐาน\'},\n];\nconst BOSS_NAMES=[\'การ์เดียนไวแวร์น\',\'แก่นแมกม่า\',\'ลีไวอาธานไครโอ\',\'ไอรอนโคลอสซัส\',\'ไฮฟ์มาเธอร์\',\'ผู้มาเยือนแห่งความว่างเปล่า\',\'โอเวอร์มายด์ป้อมปราการ\',\'ซิงกูลาริตี้ (แกนเอไอสูงสุด)\'];\n\nfunction stageConfig(n){\n  const theme=STAGE_COLORS[n-1], mul=1.2+(n-1)*(0.3/7);\n  return {\n    name:theme.name, bossName:BOSS_NAMES[n-1], theme,\n    duration:Math.round((26000+(n-1)*2500)*mul),\n    enemyHpMul:1+(n-1)*0.3, enemySpeedMul:1+(n-1)*0.1,\n    bossHp:70+n*45, spawnInterval:Math.max(1700-(n-1)*100,650)\n  };\n}\n\nconst METER_ITEMS=[\'SPEED\',\'MISSILE\',\'DOUBLE\',\'LASER\',\'RIPPLE\',\'OPTION\',\'BARRIER\'];\n\nconst SHOP_ITEMS=[\n {id:\'life\',name:\'Extra Life +1\',desc:\'เพิ่มชีวิตสำรอง 1 ดวง\',cost:80},\n {id:\'barrier\',name:\'Barrier Charge +2\',desc:\'เพิ่มพลังโล่ป้องกันทันที\',cost:50},\n {id:\'restore\',name:\'Full Power Restore\',desc:\'คืนค่าอาวุธระดับสูงทันที\',cost:140},\n {id:\'speed\',name:\'Speed Up Chip\',desc:\'เพิ่มความเร็วยานถาวร\',cost:40},\n {id:\'option\',name:\'Option Module\',desc:\'เพิ่ม Option อีก 1 ตัว\',cost:160},\n {id:\'score\',name:\'Lucky Crystal Charm\',desc:\'เพิ่มคะแนนโบนัส 500\',cost:30},\n {id:\'continue\',name:\'Continue +1\',desc:\'ซื้อสิทธิ์ Continue เพิ่ม 1 ครั้ง\',cost:300},\n];\n\n/* ---------- game state ---------- */\nlet state=\'TITLE\';\nlet score=0, crystals=0, stageIndex=1, cfgCurrent=stageConfig(1);\nlet continues=2; // 2 free Continues at the start of each new game\nlet frameCount=0, stageTime=0, spawnTimer=800;\nlet meterIndex=-1;\nlet bullets=[], eBullets=[], enemies=[], particles=[], capsules=[], crystalItems=[];\nlet boss=null, bossDying=false, bossDeathTimer=0, bossIntroTimer=0, stageClearTimer=0;\nlet pauseState=false;\nlet shakeTimer=0, shakeMag=0;\nlet posHistory=[];\n\nconst player={\n  x:50,y:BASE_H/2,w:10,h:6,\n  speeds:[1.0,1.4,1.8,2.2,2.6], speedLevel:2,\n  lives:5, hp:3, invuln:0,\n  weapon:\'normal\', missile:false, missileCooldown:0,\n  options:0, barrierCharges:0, barrierMax:0,\n  fireCooldown:0\n};\n\nfunction addShake(mag,t){ shakeMag=mag; shakeTimer=t; }\n\n/* ---------- screen helpers ---------- */\nfunction showScreen(id){\n  document.querySelectorAll(\'.screen\').forEach(el=>el.classList.add(\'hidden\'));\n  if(id) document.getElementById(id).classList.remove(\'hidden\');\n}\n\n/* ---------- game flow ---------- */\nfunction resetNewGame(){\n  score=0; crystals=0; stageIndex=1; continues=2;\n  Object.assign(player,{x:50,y:BASE_H/2,speedLevel:2,lives:5,hp:3,invuln:0,weapon:\'normal\',\n    missile:false,missileCooldown:0,options:0,barrierCharges:0,barrierMax:0,fireCooldown:0});\n  posHistory=[];\n  beginBriefing();\n}\nfunction beginBriefing(){\n  cfgCurrent=stageConfig(stageIndex);\n  stageTime=0; spawnTimer=800;\n  bullets=[]; eBullets=[]; enemies=[]; particles=[]; capsules=[]; crystalItems=[];\n  boss=null; bossDying=false; meterIndex=-1;\n  player.x=50; player.y=BASE_H/2; player.hp=3;\n  document.getElementById(\'briefStageNum\').textContent=\'STAGE \'+stageIndex+\' / 8\';\n  document.getElementById(\'briefStageName\').textContent=cfgCurrent.name;\n  document.getElementById(\'briefBossName\').textContent=\'เป้าหมาย: กำจัด \'+cfgCurrent.bossName;\n  showScreen(\'screenBriefing\'); state=\'BRIEFING\';\n}\ndocument.getElementById(\'startBtn\').onclick=()=>{ ensureAudio(); resetNewGame(); };\ndocument.getElementById(\'startStageBtn\').onclick=()=>{ showScreen(null); state=\'PLAYING\'; };\n\nfunction finishBoss(){\n  score+=1000*stageIndex; crystals+=50+stageIndex*10;\n  boss=null; bossDying=false;\n  document.getElementById(\'stageClearText\').textContent=\'โบนัส +\'+(1000*stageIndex)+\' คะแนน, +\'+(50+stageIndex*10)+\' คริสตัล\';\n  showScreen(\'screenStageClear\');\n  state=\'STAGECLEAR\'; stageClearTimer=2600;\n}\nfunction enterShop(){\n  renderShop(); showScreen(\'screenShop\'); state=\'SHOP\';\n}\nfunction renderShop(){\n  document.getElementById(\'shopCrystals\').textContent=crystals;\n  const list=document.getElementById(\'shopList\'); list.innerHTML=\'\';\n  SHOP_ITEMS.forEach(it=>{\n    const div=document.createElement(\'div\'); div.className=\'shopItem\';\n    const afford=crystals>=it.cost;\n    div.innerHTML=\'<div class="siName">\'+it.name+\'</div><div class="siDesc">\'+it.desc+\'</div><div class="siCost">\'+it.cost+\' 💎</div>\';\n    const btn=document.createElement(\'button\'); btn.textContent=\'ซื้อ\'; btn.disabled=!afford;\n    btn.onclick=()=>{ buyItem(it.id,it.cost); renderShop(); };\n    div.appendChild(btn); list.appendChild(div);\n  });\n}\nfunction buyItem(id,cost){\n  if(crystals<cost) return;\n  switch(id){\n    case \'life\': if(player.lives>=9) return; player.lives++; break;\n    case \'barrier\': player.barrierMax=Math.min(player.barrierMax+2,8); player.barrierCharges=player.barrierMax; break;\n    case \'restore\':\n      player.weapon=\'laser\'; player.missile=true;\n      player.options=Math.min(player.options+1,4);\n      player.barrierMax=Math.max(player.barrierMax,4); player.barrierCharges=player.barrierMax;\n      break;\n    case \'speed\': if(player.speedLevel>=4) return; player.speedLevel++; break;\n    case \'option\': if(player.options>=4) return; player.options++; break;\n    case \'score\': score+=500; break;\n    case \'continue\': continues++; break;\n  }\n  crystals-=cost; playTone(700,0.1,\'sine\',0.08);\n}\ndocument.getElementById(\'shopContinueBtn\').onclick=()=>{ stageIndex++; beginBriefing(); };\n\nfunction showEnding(){\n  document.getElementById(\'endScore\').textContent=score;\n  document.getElementById(\'endCrystals\').textContent=crystals;\n  showScreen(\'screenEnding\');\n}\ndocument.getElementById(\'endMenuBtn\').onclick=()=>{ state=\'TITLE\'; showScreen(\'screenTitle\'); };\n\nfunction triggerGameOver(){\n  state=\'GAMEOVER\';\n  document.getElementById(\'goScore\').textContent=score;\n  const cb=document.getElementById(\'continueBtn\');\n  cb.textContent=\'▶ Continue (\'+continues+\')\';\n  cb.disabled=continues<=0;\n  showScreen(\'screenGameOver\');\n}\ndocument.getElementById(\'continueBtn\').onclick=()=>{\n  if(continues<=0) return;\n  continues--;\n  // Continue at the current stage with fresh lives and basic ship equipment.\n  pauseState=false;\n  Object.assign(player,{x:50,y:BASE_H/2,speedLevel:2,lives:5,hp:3,invuln:0,weapon:\'normal\',\n    missile:false,missileCooldown:0,options:0,barrierCharges:0,barrierMax:0,fireCooldown:0});\n  posHistory=[];\n  beginBriefing();\n};\ndocument.getElementById(\'retryBtn\').onclick=()=>{ resetNewGame(); };\n\nfunction togglePause(){\n  if(!(state===\'PLAYING\'||state===\'BOSSINTRO\') && !pauseState) return;\n  pauseState=!pauseState;\n  showScreen(pauseState?\'screenPause\':null);\n}\ndocument.getElementById(\'resumeBtn\').onclick=()=>togglePause();\ndocument.getElementById(\'quitBtn\').onclick=()=>{ pauseState=false; state=\'TITLE\'; showScreen(\'screenTitle\'); };\n\n/* ---------- power meter ---------- */\nfunction activatePower(){\n  if(state!==\'PLAYING\'&&state!==\'BOSSINTRO\') return;\n  if(meterIndex<0) return;\n  const item=METER_ITEMS[meterIndex];\n  switch(item){\n    case \'SPEED\': player.speedLevel=Math.min(player.speedLevel+1,4); break;\n    case \'MISSILE\': player.missile=true; break;\n    case \'DOUBLE\': player.weapon=\'double\'; break;\n    case \'LASER\': player.weapon=\'laser\'; break;\n    case \'RIPPLE\': player.weapon=\'ripple\'; break;\n    case \'OPTION\': player.options=Math.min(player.options+1,4); break;\n    case \'BARRIER\': player.barrierMax=Math.min(player.barrierMax+2,8); player.barrierCharges=player.barrierMax; break;\n  }\n  meterIndex=-1; playTone(500,0.07,\'triangle\',0.08);\n}\n\n/* ---------- player damage ---------- */\nfunction damagePlayer(){\n  if(player.invuln>0) return;\n  if(player.barrierCharges>0){\n    player.barrierCharges--; player.invuln=55;\n    spawnParticles(player.x,player.y,\'#8ef9ff\',10); playTone(220,0.06,\'square\',0.08);\n    return;\n  }\n  player.hp--; player.invuln=90;\n  spawnParticles(player.x,player.y,\'#ff5050\',14); addShake(3,12); playTone(110,0.15,\'sawtooth\',0.1);\n  if(player.hp>0) return;\n  player.lives--; boom(player.x,player.y,30); addShake(5,20);\n  if(player.lives<=0){ triggerGameOver(); return; }\n  player.weapon=\'normal\'; player.missile=false; player.options=0;\n  player.barrierMax=0; player.barrierCharges=0; player.hp=3;\n  player.speedLevel=Math.max(2,player.speedLevel-1);\n  player.x=50; player.y=BASE_H/2; player.invuln=150; eBullets.length=0;\n}\n\n/* ---------- sprite toolkit (procedural pixel art + auto outline) ---------- */\nconst SIL=new Map(), GL={}, OLC=[7,9,18];\nfunction shade(h,f){const n=parseInt(h.slice(1),16);let r=n>>16,g=(n>>8)&255,b=n&255;\n  if(f<1){r*=f;g*=f;b*=f;}else{const t=f-1;r+=(255-r)*t;g+=(255-g)*t;b+=(255-b)*t;}\n  return \'rgb(\'+(r|0)+\',\'+(g|0)+\',\'+(b|0)+\')\';}\nfunction hx(h,a){const n=parseInt(h.slice(1),16);return \'rgba(\'+(n>>16)+\',\'+((n>>8)&255)+\',\'+(n&255)+\',\'+a+\')\';}\nfunction cv(w,h){const c=document.createElement(\'canvas\');c.width=w;c.height=h;return c;}\nfunction fin(c,flip){\n  const g=c.getContext(\'2d\'),w=c.width,h=c.height,s=g.getImageData(0,0,w,h).data,o=g.createImageData(w,h),t=o.data;\n  const a=(x,y)=>x>=0&&y>=0&&x<w&&y<h&&s[(y*w+x)*4+3]>127;\n  for(let y=0;y<h;y++)for(let x=0;x<w;x++){const i=(y*w+x)*4;\n    if(s[i+3]>127){t[i]=s[i];t[i+1]=s[i+1];t[i+2]=s[i+2];t[i+3]=255;}\n    else if(a(x-1,y)||a(x+1,y)||a(x,y-1)||a(x,y+1)){t[i]=OLC[0];t[i+1]=OLC[1];t[i+2]=OLC[2];t[i+3]=255;}}\n  g.putImageData(o,0,0);\n  if(flip){const f=cv(w,h),q=f.getContext(\'2d\');q.scale(-1,1);q.drawImage(c,-w,0);return f;}\n  return c;\n}\nfunction mk(rows,cols,sym,flip){\n  const w=Math.max(...rows.map(r=>r.length)),h=rows.length,H=sym?h*2-1:h,c=cv(w+2,H+2),g=c.getContext(\'2d\');\n  const put=(x,y,k)=>{g.fillStyle=cols[\'abcde\'.indexOf(k)];g.fillRect(x+1,y+1,1,1);};\n  rows.forEach((r,y)=>{for(let x=0;x<r.length;x++){const k=r[x];if(\'abcde\'.indexOf(k)<0)continue;put(x,y,k);if(sym&&y<h-1)put(x,H-1-y,k);}});\n  return fin(c,flip);\n}\nfunction sil(c){let s=SIL.get(c);if(!s){s=cv(c.width,c.height);const g=s.getContext(\'2d\');g.drawImage(c,0,0);g.globalCompositeOperation=\'source-in\';g.fillStyle=\'#fff\';g.fillRect(0,0,s.width,s.height);SIL.set(c,s);}return s;}\nfunction glow(col,r){const k=col+r;if(GL[k])return GL[k];const c=cv(r*2,r*2),g=c.getContext(\'2d\'),q=g.createRadialGradient(r,r,0,r,r,r);q.addColorStop(0,col);q.addColorStop(1,\'rgba(0,0,0,0)\');g.fillStyle=q;g.fillRect(0,0,r*2,r*2);return GL[k]=c;}\nfunction gl(col,r,x,y,a){ctx.globalCompositeOperation=\'lighter\';ctx.globalAlpha=a==null?1:a;ctx.drawImage(glow(col,r),Math.round(x-r),Math.round(y-r));ctx.globalCompositeOperation=\'source-over\';ctx.globalAlpha=1;}\nfunction spr(im,x,y){ctx.drawImage(im,Math.round(x-im.width/2),Math.round(y-im.height/2));}\n\n/* player ship: Vic-Viper style interceptor */\nconst PS=mk(["......bb","....bbcb","...bbbbb........bb","..bbbbbbbbbbaaaabbcb",".bbaaaaaaaaaaaaaaaaaaab","dbaaaaaaaaaaaacccaaaaaaaa","ddaaaaaaaaccccceeeaaaaaaaaaa"],[\'#6fd3ff\',\'#2a5fb8\',\'#e8fbff\',\'#ff9a2e\',\'#ffffff\'],1,0);\nconst CAP=mk(["..bbbb..",".baaaab.","bacccaab","baceecab"],[\'#46ff8f\',\'#128a4a\',\'#c8ffe0\',\'#fff\',\'#fff\'],1,0);\nconst CRY=mk(["...b...","..bab..",".bacab.","bacceab"],[\'#5ec8ff\',\'#1c5fa8\',\'#d8f4ff\',\'#fff\',\'#fff\'],1,0);\n/* bullets */\nconst EB=[0,1,2,3].map(k=>{const s=[11,13,17,15][k],c=cv(s,s),g=c.getContext(\'2d\'),m=s/2;\n  const dot=(r,f)=>{g.fillStyle=f;g.beginPath();g.arc(m,m,r,0,7);g.fill();};\n  const dia=(r,f)=>{g.fillStyle=f;g.beginPath();g.moveTo(m,m-r);g.lineTo(m+r,m);g.lineTo(m,m+r);g.lineTo(m-r,m);g.fill();};\n  if(k==0){dot(5,\'#070912\');dot(3.6,\'#ff2d6b\');dot(1.8,\'#fff\');}\n  else if(k==1){g.fillStyle=\'#070912\';g.fillRect(0,4,13,5);g.fillStyle=\'#ff2d6b\';g.fillRect(1,5,11,3);g.fillStyle=\'#fff\';g.fillRect(6,6,6,1);}\n  else if(k==2){dot(8,\'#070912\');dot(6.5,\'#ff7a1a\');dot(4.5,\'#ffd23a\');dot(2.4,\'#fff\');}\n  else{dia(7.5,\'#070912\');dia(6,\'#ff3b2f\');dia(4,\'#ffd23a\');dia(1.8,\'#fff\');}\n  return c;});\nconst EBG=[\'rgba(255,45,107,.6)\',\'rgba(255,45,107,.6)\',\'rgba(255,140,30,.7)\',\'rgba(255,70,40,.7)\'];\n\n/* enemies (Detailed Alien Spaceships; unlock stage u) */\nconst ES={};\nfunction defE(k,u,hp,sp,sc,cr,rows,cols,sym,flip,hv){const im=mk(rows,cols,sym,flip);ES[k]={u,hp,sp,sc,cr,img:im,w:im.width-4,h:im.height-4,hv};}\ndefE(\'drone\',1,2,1.3,50,.15,[\n  "........bbbb......",\n  ".....bbbaaaabb....",\n  "...bbaaaaaaaacbb..",\n  ".bbbaaaacccccaaabb",\n  "dbaaaaaaceeeeaaaab",\n  "ddbaaaaacccccaaabb",\n  "...bbbaaaaaaabbb.."\n],[\'#ff6b6b\',\'#8e1c34\',\'#ffc4c4\',\'#ffe27a\',\'#fff\'],1,1);\ndefE(\'rock\',1,3,1,30,.1,[\n  "......bbbbbb......",\n  "...bbbaaaaaabbb...",\n  ".bbaaaacccccaaaabb",\n  "bbaaaaceeeeeecaaab",\n  "dbaaaaaaaaaaaaaaab",\n  ".bbbaaaababaaaabb.",\n  "...bbbbbaaaabbbb.."\n],[\'#9b8cff\',\'#483494\',\'#dcd6ff\',\'#4ef0ff\',\'#fff\'],1,1);\ndefE(\'carrier\',1,4,.9,150,1,[\n  "....bbbb....bbbb....",\n  "..bbbaabbbbbbaabbb..",\n  ".bbaaaaaaaaaaaaaabb.",\n  "bbaaaaccccccccaaaabb",\n  "dbaaaaceeeeeeeecaaab",\n  "ddbaaaaddddddddaaabb"\n],[\'#ffd84d\',\'#a8731a\',\'#fff2a8\',\'#46ff8f\',\'#fff\'],1,1);\ndefE(\'turret\',1,5,.7,120,.25,[\n  ".....bbbbbbbb.....",\n  "...bbaaaaaaaabb...",\n  ".bbbaaccccccaabbb.",\n  "bbaaaaceeeeeecaaab",\n  "dbaaaaddaaaaaddabb",\n  "..bbbb..bbbb..bb.."\n],[\'#b06bff\',\'#4d2a8f\',\'#e3c8ff\',\'#ff4d6d\',\'#fff\'],1,1);\ndefE(\'swooper\',2,3,1.5,90,.2,[\n  "bb..............",\n  ".bbbb.....bbbb..",\n  "..bbbbaaaabbbbb.",\n  "...bbaaaaaaaacbb",\n  "ddbaaaaacccceeaa",\n  "dddbaaaaaaaaaabb"\n],[\'#ff9a3d\',\'#9c3d12\',\'#ffd9a8\',\'#4ef0ff\',\'#fff\'],1,1);\ndefE(\'spinner\',2,5,1.1,140,.3,[\n  "......bbbbbb......",\n  "...bbbaaaaaabbb...",\n  ".bbaaaacccccaaaabb",\n  "dbaaaaceeeeeecaaad",\n  "ddbaaaacccccaaaabb",\n  "...bbbaaaaaabbb..."\n],[\'#4ef0a8\',\'#157a5c\',\'#c8ffe8\',\'#ffe27a\',\'#fff\'],1,1);\ndefE(\'wasp\',3,4,1.4,130,.25,[\n  "bbb........bbb....",\n  ".bbbb....bbbbbb...",\n  "..bbbbaaaabbbbb...",\n  "...bbaaaaaaacccbb.",\n  "ddbaaaaacccceeeeaa",\n  "dddbaaaaaaaaaabbb."\n],[\'#ffe14d\',\'#7a5a10\',\'#fff6b0\',\'#ff4d4d\',\'#fff\'],1,1);\ndefE(\'gunship\',4,16,1.2,500,.8,[\n  "......bbbbbbbb........",\n  "...bbbaaaaaaaabbbb....",\n  ".bbbaaaaaaaaaaaaaabb..",\n  "bbaaaacccccccccaaaabbb",\n  "dbaaaaceeeeeeeeecaaaab",\n  "ddbaaaaaaaaaaaaaaaaabb",\n  "..bbbb..bbbbbb..bbbb.."\n],[\'#6f86ff\',\'#2a3a96\',\'#cfd8ff\',\'#ff9a2e\',\'#fff\'],1,1,1);\ndefE(\'mine\',4,3,.8,80,.2,[\n  "..bb....bbbb....bb..",\n  "...bbbbaaaaaabbbb...",\n  "....bbaaccccaabb....",\n  ".bbbaaaaceeeecaaabbb",\n  "ddbaaaaadddddaaaaabb"\n],[\'#8a8a9a\',\'#3a3a4a\',\'#d0d0e0\',\'#ff3d3d\',\'#fff\'],1,1);\ndefE(\'sniper\',5,7,1.2,250,.5,[\n  "..........bbbbbb....",\n  "......bbbbaaaaaabb..",\n  "..bbbbaaaaaaaaaaaabb",\n  "bbaaaaaaccccccccaaaa",\n  "ddbaaaaaceeeeeeeecaa"\n],[\'#ff5de0\',\'#7a1f6a\',\'#ffc8f4\',\'#4ef0ff\',\'#fff\'],1,1);\ndefE(\'phantom\',6,6,1.1,300,.5,[\n  "....bbbb....bbbb....",\n  "..bbaaaab..baaaabb..",\n  ".bbaaaaaaaaaaaaaabb.",\n  "bbaaaaccccccccaaaabb",\n  "dbaaaaceeeeeeeecaaab",\n  "..bbbbaaaaaaaaaabbb."\n],[\'#9d7bff\',\'#3b2b8a\',\'#d8ccff\',\'#7fffd4\',\'#fff\'],1,1);\ndefE(\'kamikaze\',6,4,2.4,200,.3,[\n  "......bbbb........",\n  "...bbbaaaabbb.....",\n  ".bbaaaaaaaaaabbb..",\n  "dbaaaaccccccceeeaa",\n  "ddbaaaaaaaaaabbb.."\n],[\'#ff3d3d\',\'#7a1010\',\'#ffb0b0\',\'#ffe27a\',\'#fff\'],1,1);\ndefE(\'elite\',7,26,1,800,1,[\n  "........bbbbbbbb..........",\n  ".....bbbaaaaaaaabbb.......",\n  "...bbbaaaacccccaaaabbb....",\n  ".bbbaaaaaaaaaaaaaaaaabbb..",\n  "bbaaaacccccccccccccaaaabbb",\n  "dbaaaaceeeeeeeeeeeecaaaaab",\n  "ddbbaaaaaaaaaaaaaaaaaaaabb"\n],[\'#2fd6a0\',\'#0f6a5a\',\'#b8ffe8\',\'#ffd84d\',\'#fff\'],1,1,1);\n\n/* bosses: procedural pixel-art, shaded + outlined */\nfunction bossSpr(n){\n  const A=STAGE_COLORS[n-1].accent,W=[96,92,128,86,104,100,136,116][n-1],H=[76,94,70,104,96,100,92,116][n-1];\n  const c=cv(W+4,H+4),g=c.getContext(\'2d\');g.translate(2,2);\n  const cx=W/2,cy=H/2,D=shade(A,.25),M=shade(A,.55),L=shade(A,1);\n  const pl=(p,f)=>{g.fillStyle=f;g.beginPath();p.forEach((q,i)=>i?g.lineTo(q[0],q[1]):g.moveTo(q[0],q[1]));g.closePath();g.fill();};\n  const el=(x,y,rx,ry,f)=>{g.fillStyle=f;g.beginPath();g.ellipse(x,y,rx,ry,0,0,7);g.fill();};\n  const blob=(x,y,rx,ry)=>{el(x,y,rx,ry,D);el(x-1,y-1,rx-2,ry-2,M);el(x-2,y-3,rx*.55,ry*.5,L);};\n  const rc=(x,y,w,h)=>{g.fillStyle=D;g.fillRect(x,y,w,h);g.fillStyle=M;g.fillRect(x+1,y+1,w-2,h-2);g.fillStyle=L;g.fillRect(x+1,y+1,w-2,1);};\n  const sym=f=>{f();g.save();g.translate(0,H);g.scale(1,-1);f();g.restore();};\n  let core=[cx,cy];\n  if(n==1){sym(()=>{pl([[cx-6,cy-6],[cx+14,3],[cx+42,6],[cx+26,cy-8]],D);pl([[cx-2,cy-7],[cx+14,7],[cx+34,8],[cx+22,cy-9]],M);rc(cx-26,cy-22,16,6);});\n    pl([[cx+28,cy-4],[W-2,cy],[cx+28,cy+4]],M);blob(cx+2,cy,30,15);blob(cx-30,cy,14,10);core=[cx-32,cy];}\n  else if(n==2){for(let i=0;i<12;i++){const a=i*.5236;pl([[cx+Math.cos(a-.18)*30,cy+Math.sin(a-.18)*30],[cx+Math.cos(a)*45,cy+Math.sin(a)*45],[cx+Math.cos(a+.18)*30,cy+Math.sin(a+.18)*30]],D);}\n    blob(cx,cy,32,32);el(cx,cy,16,16,D);}\n  else if(n==3){for(let i=0;i<6;i++){const x=W-14-i*14,r=7+(5-i)*1.3;pl([[x-4,cy-r],[x+2,cy-r-9],[x+6,cy-r]],M);pl([[x-4,cy+r],[x+2,cy+r+9],[x+6,cy+r]],M);blob(x,cy,r+3,r);}\n    blob(24,cy,20,15);pl([[6,cy+7],[38,cy+9],[28,cy+20]],M);core=[22,cy-3];}\n  else if(n==4){rc(cx-18,cy-30,36,60);sym(()=>{rc(cx-36,cy-42,26,16);rc(cx-46,cy-38,14,6);rc(cx-24,cy-48,18,10);});blob(cx-4,16,13,11);core=[cx-4,cy];}\n  else if(n==5){g.strokeStyle=D;g.lineWidth=3;[[-40,-30],[-40,30],[40,-30],[40,30]].forEach(p=>{g.beginPath();g.moveTo(cx,cy);g.lineTo(cx+p[0],cy+p[1]);g.stroke();});\n    [[cx-26,cy-22,14,13],[cx-26,cy+22,14,13],[cx+26,cy-24,15,14],[cx+24,cy+24,15,14],[cx+38,cy,12,12],[cx-38,cy,11,11],[cx,cy,28,28]].forEach(p=>blob(p[0],p[1],p[2],p[3]));}\n  else if(n==6){sym(()=>{pl([[cx-34,cy-24],[cx-46,cy-46],[cx-18,cy-34]],M);pl([[cx+34,cy-24],[cx+46,cy-46],[cx+18,cy-34]],M);});\n    el(cx,cy,46,46,D);el(cx,cy,42,42,M);el(cx,cy,34,34,\'#0a0612\');blob(cx,cy,26,26);}\n  else if(n==7){rc(14,cy-14,108,28);rc(30,cy-24,70,12);sym(()=>{rc(cx-40,cy-38,18,12);rc(cx+6,cy-38,18,12);rc(cx-52,cy-34,14,4);});\n    rc(W-22,cy-10,18,20);pl([[2,cy],[22,cy-14],[22,cy+14]],M);rc(cx+20,cy-34,22,10);core=[cx-30,cy];}\n  else{for(const r of [56,46]){el(cx,cy,r,r,D);el(cx,cy,r-2,r-2,M);}for(let i=0;i<8;i++){g.save();g.translate(cx,cy);g.rotate(i*.785);rc(34,-7,20,14);g.restore();}\n    blob(cx,cy,32,32);el(cx,cy,13,13,\'#05030a\');}\n  const im=fin(c);im.core=[core[0]+2,core[1]+2];return im;\n}\nconst BP=[[\'fan\',\'ring\',\'minions\'],[\'fan\',\'rain\',\'ring\',\'charge\'],[\'aim\',\'wall\',\'ring\',\'minions\'],[\'fan\',\'wall\',\'sweep\',\'charge\'],[\'rain\',\'homing\',\'ring\',\'minions\'],[\'sweep\',\'aim\',\'homing\',\'wall\'],[\'fan\',\'wall\',\'sweep\',\'rain\',\'minions\'],[\'sweep\',\'ring\',\'wall\',\'homing\',\'aim\',\'rain\',\'charge\',\'fan\']];\n\n/* ---------- entities ---------- */\nfunction makeBullet(x,y,vx,vy,type){\n  const pierce=type===\'laser\'?3:(type===\'ripple\'?2:1), dmg=type===\'laser\'?2:(type===\'missile\'?3:(type===\'ripple\'?2:1));\n  return {x,y,vx,vy,type,w:type===\'laser\'?16:(type===\'ripple\'?6:6),h:type===\'ripple\'?14:3,pierce,dmg,ph:rand(0,6.28),r:2};\n}\nfunction eb(x,y,a,s,k){k=k||0;s*=1+(stageIndex-1)*.035;eBullets.push({x,y,vx:Math.cos(a)*s,vy:Math.sin(a)*s,k,r:k>1?3.6:2.2,a,s,h:0});return eBullets[eBullets.length-1];}\nfunction ring(x,y,n,s,off,k){for(let i=0;i<n;i++)eb(x,y,off+i*6.2832/n,s,k);}\nfunction fanAt(x,y,n,sp,s,k){const a=Math.atan2(player.y-y,player.x-x);for(let i=0;i<n;i++)eb(x,y,a+(i-(n-1)/2)*sp,s,k);}\nfunction makeEnemy(type,x,y){\n  const t=ES[type],m=cfgCurrent.enemyHpMul,hp=Math.ceil(t.hp*(t.hv?1+(m-1)*.5:m));\n  const scale=t.hv?1.15:1.0;\n  return {type,x,y,y0:y,w:t.img.width*scale-4,h:t.img.height*scale-4,drawScale:scale,hp,maxhp:hp,sp:t.sp*cfgCurrent.enemySpeedMul,ph:rand(0,6.28),t:0,st:rand(40,110),data:t,hv:t.hv,fl:0,dir:Math.random()<.5?1:-1,ch:0,sa:0,vx:0,vy:0};\n}\nfunction spawnParticles(x,y,color,count){\n  for(let i=0;i<count;i++){const a=rand(0,6.28),sp=rand(.5,3);particles.push({x,y,vx:Math.cos(a)*sp,vy:Math.sin(a)*sp,life:rand(15,35),maxlife:35,color,size:rand(1,3)});}\n}\nfunction boom(x,y,r){rings.push({x,y,r:2,max:r,life:1});spawnParticles(x,y,\'#ffb347\',Math.ceil(r/2));spawnParticles(x,y,\'#fff4c0\',Math.ceil(r/5));}\nconst rings=[];\n\nfunction tryPlayerFire(dt){\n  player.fireCooldown-=dt;\n  if(isFiring()&&player.fireCooldown<=0){\n    fireSet(player.x+8,player.y);\n    for(let i=0;i<player.options;i++){const p=getOptionPos(i);fireSet(p.x+3,p.y);}\n    player.fireCooldown=player.weapon===\'laser\'?9:(player.weapon===\'ripple\'?11:7);\n    playTone(player.weapon===\'laser\'?320:520,.035,\'square\',.04);\n  }\n  if(player.missile){\n    player.missileCooldown-=dt;\n    if(isFiring()&&player.missileCooldown<=0){bullets.push(makeBullet(player.x+2,player.y+4,2.2,1.1,\'missile\'));player.missileCooldown=50;}\n  }\n}\nfunction fireSet(x,y){\n  switch(player.weapon){\n    case \'double\':bullets.push(makeBullet(x,y,3.6,0,\'normal\'));bullets.push(makeBullet(x,y,2.8,-2.4,\'normal\'));break;\n    case \'laser\':bullets.push(makeBullet(x,y,4.6,0,\'laser\'));break;\n    case \'ripple\':bullets.push(makeBullet(x,y,2.6,0,\'ripple\'));break;\n    default:bullets.push(makeBullet(x,y,3.6,0,\'normal\'));\n  }\n}\nfunction updateTrail(){posHistory.unshift({x:player.x,y:player.y});if(posHistory.length>240)posHistory.pop();}\nfunction getOptionPos(i){return posHistory[Math.min((i+1)*14,posHistory.length-1)]||{x:player.x,y:player.y};}\n\nfunction spawnWave(){\n  const av=Object.keys(ES).filter(k=>ES[k].u<=stageIndex);\n  if(Math.random()<.22){ // V-formation\n    const F=[\'drone\',\'swooper\',\'wasp\'].filter(k=>ES[k].u<=stageIndex),t=F[Math.floor(rand(0,F.length))],y0=rand(60,BASE_H-60);\n    for(let i=0;i<5;i++)enemies.push(makeEnemy(t,BASE_W+12+Math.abs(i-2)*16,y0+(i-2)*15));\n    return;\n  }\n  const pool=[];av.forEach(k=>{const w=ES[k].u>=Math.max(2,stageIndex-2)?3:1;for(let i=0;i<w;i++)pool.push(k);});\n  const count=1+Math.floor(Math.random()*Math.min(3,1+Math.floor(stageIndex/3)));\n  for(let i=0;i<count;i++){\n    let t=pool[Math.floor(rand(0,pool.length))];\n    if(ES[t].hv&&enemies.some(e=>e.hv))t=\'drone\';\n    enemies.push(makeEnemy(t,BASE_W+14+i*22,rand(24,BASE_H-24)));\n  }\n}\nfunction tick(e,dt,lo,hi){e.st-=dt;if(e.st<=0){e.st=rand(lo,hi);return true;}return false;}\nfunction updateEnemies(dt){\n  for(let i=enemies.length-1;i>=0;i--){\n    const e=enemies[i];e.t+=dt;if(e.fl>0)e.fl-=dt;\n    const a=Math.atan2(player.y-e.y,player.x-e.x);\n    switch(e.type){\n      case \'drone\':e.x-=e.sp*dt;e.y+=Math.sin(e.t*.06+e.ph)*.6*dt;if(tick(e,dt,90,170))eb(e.x,e.y,a,1.8,0);break;\n      case \'rock\':e.x-=e.sp*dt;e.y+=Math.sin(e.ph)*.15*dt;break;\n      case \'carrier\':e.x-=e.sp*dt;e.y+=Math.sin(e.t*.04+e.ph)*.4*dt;if(tick(e,dt,160,260))eb(e.x,e.y,a,1.6,0);break;\n      case \'turret\':e.x-=e.sp*dt;if(tick(e,dt,90,150))fanAt(e.x,e.y,3,.28,1.8,0);break;\n      case \'swooper\':e.x-=e.sp*1.1*dt;e.y=e.y0+Math.sin(e.t*.045+e.ph)*70;if(e.y<12)e.y=12;if(e.y>BASE_H-12)e.y=BASE_H-12;if(tick(e,dt,100,160))eb(e.x,e.y,a,2,0);break;\n      case \'spinner\':e.x-=e.sp*.5*dt;e.y=e.y0+Math.sin(e.t*.07)*38;e.sa+=.35;if(tick(e,dt,120,170))ring(e.x,e.y,8,1.4,e.sa,0);break;\n      case \'wasp\':e.x-=e.sp*dt;if(Math.floor(e.t/45)%2)e.y+=1.6*dt;else e.y-=1.6*dt;e.y=clamp(e.y,12,BASE_H-12);if(tick(e,dt,80,120))fanAt(e.x,e.y,3,.12,2.5,1);break;\n      case \'gunship\':\n        if(e.t<400){if(e.x>BASE_W-70)e.x-=e.sp*1.2*dt;e.y=e.y0+Math.sin(e.t*.02)*40;\n          if(tick(e,dt,60,90)){if(e.sa++%2)fanAt(e.x,e.y,5,.22,2,0);else{fanAt(e.x,e.y-6,1,0,1.3,2);fanAt(e.x,e.y+6,1,0,1.3,2);}}}\n        else{e.x+=1.2*dt;}break;\n      case \'mine\':e.x-=e.sp*.5*dt;if(Math.hypot(player.x-e.x,player.y-e.y)<30){ring(e.x,e.y,8,1.8,0,0);boom(e.x,e.y,14);enemies.splice(i,1);continue;}break;\n      case \'sniper\':\n        if(e.t<500){if(e.x>BASE_W-50)e.x-=e.sp*dt;e.y+=(player.y-e.y)*.01*dt;\n          if(e.ch>0){e.ch-=dt;if(e.ch<=0)eb(e.x,e.y,Math.atan2(player.y-e.y,player.x-e.x),4.4,1);}\n          else if(tick(e,dt,120,180))e.ch=50;}\n        else e.x+=1.2*dt;break;\n      case \'phantom\':e.x-=e.sp*.7*dt;e.al=.5+.5*Math.sin(e.t*.05+e.ph);\n        if(Math.floor(e.t)%170===0)e.y=rand(24,BASE_H-24);\n        if(tick(e,dt,90,140)){for(let k=0;k<4;k++)eb(e.x,e.y,.785+k*1.571,1.8,0);fanAt(e.x,e.y,1,0,2.2,1);}break;\n      case \'kamikaze\':\n        if(e.t<45){e.x-=.5*dt;e.y+=(player.y-e.y)*.05*dt;e.vx=Math.cos(a)*e.sp;e.vy=Math.sin(a)*e.sp;}\n        else{e.x+=e.vx*dt;e.y+=e.vy*dt;}break;\n      case \'elite\':\n        if(e.t<900){if(e.x>BASE_W-80)e.x-=e.sp*dt;e.y=e.y0+Math.sin(e.t*.015)*50;e.sa+=.3*dt;\n          if(Math.floor(e.t)%6===0){eb(e.x,e.y,e.sa,1.9,0);eb(e.x,e.y,e.sa+3.14,1.9,0);}\n          if(tick(e,dt,150,200))fanAt(e.x,e.y,3,.3,1.7,2);}\n        else e.x+=1.3*dt;break;\n    }\n    if(e.x<-30||e.y<-30||e.y>BASE_H+30||(e.x>BASE_W+60&&e.t>60))enemies.splice(i,1);\n  }\n}\nfunction updateBullets(dt){\n  for(let i=bullets.length-1;i>=0;i--){\n    const b=bullets[i];b.x+=b.vx*dt;b.y+=b.vy*dt;\n    if(b.type===\'ripple\'){b.ph+=.15*dt;b.y+=Math.sin(b.ph)*.6*dt;b.h=Math.min(22,b.h+.35*dt);}\n    if(b.type===\'missile\'){b.vy*=.97;if(Math.random()<.5)particles.push({x:b.x-4,y:b.y,vx:-.5,vy:0,life:12,maxlife:12,color:\'#ffb347\',size:2});}\n    if(b.x>BASE_W+20||b.x<-20||b.y<-20||b.y>BASE_H+20)bullets.splice(i,1);\n  }\n}\nfunction updateEBullets(dt){\n  for(let i=eBullets.length-1;i>=0;i--){\n    const b=eBullets[i];\n    if(b.h>0){b.h-=dt;let d=Math.atan2(player.y-b.y,player.x-b.x)-b.a;d=Math.atan2(Math.sin(d),Math.cos(d));b.a+=clamp(d,-.04,.04)*dt;b.vx=Math.cos(b.a)*b.s;b.vy=Math.sin(b.a)*b.s;}\n    b.x+=b.vx*dt;b.y+=b.vy*dt;\n    if(b.x<-20||b.x>BASE_W+20||b.y<-20||b.y>BASE_H+20)eBullets.splice(i,1);\n  }\n}\nfunction updateParticles(dt){\n  for(let i=particles.length-1;i>=0;i--){const p=particles[i];p.x+=p.vx*dt;p.y+=p.vy*dt;p.life-=dt;if(p.life<=0)particles.splice(i,1);}\n  for(let i=rings.length-1;i>=0;i--){const r=rings[i];r.r+=(r.max-r.r)*.15*dt+.3;r.life-=.05*dt;if(r.life<=0)rings.splice(i,1);}\n}\n/* items: magnet pull + return trip (wait 20s) */\nconst MAG=70;\nfunction newItem(arr,x,y,w){arr.push({x,y,w,h:w,st:0,ph:rand(0,6),wait:20000,tx:0,ty:0});}\nfunction updateItems(dt){\n  for(const arr of [capsules,crystalItems])for(let i=arr.length-1;i>=0;i--){\n    const c=arr[i],dx=player.x-c.x,dy=player.y-c.y,d=Math.hypot(dx,dy)||1;\n    c.mag=false;\n    if(c.st<3&&d<MAG){const s=Math.min(d,(2.4+(MAG-d)*.06)*dt);c.x+=dx/d*s;c.y+=dy/d*s;c.mag=true;if(c.st===2)c.wait-=dt*16.667;continue;}\n    if(c.st===0){c.x-=dt;c.y+=Math.sin(frameCount*.1+c.ph)*.3*dt;if(c.x<4){c.st=1;c.x=-6;c.tx=rand(60,150);c.ty=clamp(c.y,24,BASE_H-24);}}\n    else if(c.st===1){c.x+=Math.max(1.5,(c.tx-c.x)*.06)*dt;c.y+=(c.ty-c.y)*.06*dt;if(c.x>=c.tx-3)c.st=2;}\n    else if(c.st===2){c.y+=Math.sin(frameCount*.08+c.ph)*.3*dt;c.wait-=dt*16.667;if(c.wait<=0)c.st=3;}\n    else{c.x-=1.6*dt;if(c.x<-12)arr.splice(i,1);}\n  }\n}\nfunction killEnemy(e,idx){\n  score+=e.data.sc;boom(e.x,e.y,e.hv?30:12);playTone(150,.07,\'square\',.06);\n  if(e.type===\'mine\')ring(e.x,e.y,8,1.8,0,0);\n  if(e.data.cr>=1||Math.random()<.15)newItem(capsules,e.x,e.y,9);\n  else if(Math.random()<e.data.cr)newItem(crystalItems,e.x,e.y,7);\n  if(e.hv)for(let i=0;i<3;i++)newItem(crystalItems,e.x+rand(-12,12),e.y+rand(-12,12),7);\n  enemies.splice(idx,1);\n}\nfunction collectCapsule(){meterIndex=(meterIndex+1)%7;score+=10;playTone(620,.05,\'triangle\',.06);}\n\n/* ---------- boss AI ---------- */\nconst PT={\n  fan:b=>fanAt(b.x-20,b.y,5+(b.rg?2:0),.2,2.2,2),\n  ring:b=>ring(b.x-10,b.y,14+(b.rg?6:0),1.7,rand(0,6),3),\n  sweep:b=>{b.burst={n:26,gap:4,i:0,cd:0,fn:i=>{const a=Math.PI+Math.sin(i*.35)*1.1;for(let k=-1;k<=1;k++)eb(b.x-20,b.y,a+k*.28,2,0);}};},\n  rain:b=>{b.burst={n:16,gap:6,i:0,cd:0,fn:()=>eb(rand(60,BASE_W-10),-4,Math.PI/2+rand(-.15,.35),1.9,1)};},\n  wall:b=>{const g=Math.floor(rand(1,10));for(let i=0;i<12;i++)if(Math.abs(i-g)>1)eb(b.x-b.w/2,14+i*16,Math.PI,1.5,3);},\n  aim:b=>{b.burst={n:10,gap:5,i:0,cd:0,fn:()=>fanAt(b.x-20,b.y,1,0,3.2,1)};},\n  homing:b=>{for(let i=-1;i<=1;i++)eb(b.x-20,b.y+i*14,Math.PI+i*.5,1.3,2).h=110;},\n  minions:b=>{if(enemies.length>8)return;const L=[\'drone\',\'swooper\',\'wasp\',\'kamikaze\'].filter(k=>ES[k].u<=stageIndex);for(let i=0;i<3;i++)enemies.push(makeEnemy(L[Math.floor(rand(0,L.length))],b.x-10,b.y-24+i*24));},\n  charge:b=>{b.dash=1;b.dt=0;}\n};\nfunction updateBoss(dt){\n  const b=boss;if(b.flash>0)b.flash-=dt;\n  if(b.entryTimer>0){b.x-=.8*dt;if(b.x<=b.hx)b.entryTimer=0;return;}\n  b.t+=dt;b.rg=b.hp<b.maxHp*.5;\n  if(b.dash){\n    b.dt+=dt;\n    if(b.dash===1){if(b.dt>45){b.dash=2;}}\n    else if(b.dash===2){b.x-=4.5*dt;if(b.x<70)b.dash=3;}\n    else{b.x+=2*dt;if(b.x>=b.hx){b.x=b.hx;b.dash=0;}}\n    b.y+=(player.y-b.y)*.02*dt;\n  }else{\n    b.y+=Math.sin(b.t*.025)*.6*dt*(b.rg?1.4:1);b.x=b.hx+Math.sin(b.t*.012)*8;\n    if(b.burst){b.burst.cd-=dt;if(b.burst.cd<=0){b.burst.fn(b.burst.i++);b.burst.cd=b.burst.gap;if(b.burst.i>=b.burst.n)b.burst=null;}}\n    b.attackTimer-=dt;\n    if(b.attackTimer<=0&&!b.burst){\n      const L=BP[stageIndex-1];PT[L[b.pi++%L.length]](b);playTone(130,.08,\'sawtooth\',.07);\n      b.attackTimer=Math.max(80-stageIndex*3,40)*(b.rg?.75:1);\n    }\n  }\n  b.y=clamp(b.y,b.h/2+4,BASE_H-b.h/2-4);\n}\nfunction startBossFight(){\n  const im=bossSpr(stageIndex);\n  boss={name:cfgCurrent.bossName,hp:cfgCurrent.bossHp,maxHp:cfgCurrent.bossHp,img:im,x:BASE_W+im.width/2+10,y:BASE_H/2,hx:BASE_W-im.width/2-14,\n    w:im.width*.78,h:im.height*.78,entryTimer:999,attackTimer:60,pi:0,t:0,flash:0,dash:0,dt:0,rg:false,burst:null,color:cfgCurrent.theme.accent};\n  document.getElementById(\'bossNameTag\').textContent=boss.name;\n  state=\'BOSSINTRO\';bossIntroTimer=110;\n}\n\n/* ---------- collisions ---------- */\nfunction handleCollisions(){\n  for(let i=bullets.length-1;i>=0;i--){\n    const b=bullets[i];let consumed=false;\n    for(let j=enemies.length-1;j>=0;j--){\n      const e=enemies[j];\n      if(rectHit(b,e)){e.hp-=b.dmg;e.fl=4;spawnParticles(b.x,b.y,\'#9fffc8\',3);b.pierce--;if(e.hp<=0)killEnemy(e,j);if(b.pierce<=0){consumed=true;break;}}\n    }\n    if(!consumed&&boss&&!bossDying&&boss.entryTimer<=0&&rectHit(b,boss)){\n      boss.hp-=b.dmg;boss.flash=3;spawnParticles(b.x,b.y,\'#ffffff\',3);b.pierce--;\n      if(boss.hp<=0){boss.hp=0;bossDying=true;bossDeathTimer=130;eBullets.length=0;addShake(5,40);}\n      if(b.pierce<=0)consumed=true;\n    }\n    if(consumed)bullets.splice(i,1);\n  }\n  for(let i=eBullets.length-1;i>=0;i--){\n    const b=eBullets[i];if(!b)continue;\n    if(Math.abs(b.x-player.x)<b.r+4&&Math.abs(b.y-player.y)<b.r+2.5){eBullets.splice(i,1);damagePlayer();}\n  }\n  for(let i=enemies.length-1;i>=0;i--){\n    if(enemies[i]&&rectHit(enemies[i],player)){if(enemies[i].hv)damagePlayer();else{killEnemy(enemies[i],i);damagePlayer();}}\n  }\n  if(boss&&!bossDying&&rectHit(boss,player))damagePlayer();\n  for(const [arr,fn] of [[capsules,collectCapsule],[crystalItems,()=>{crystals+=10;score+=20;playTone(900,.05,\'sine\',.06);}]])\n    for(let i=arr.length-1;i>=0;i--)if(Math.hypot(arr[i].x-player.x,arr[i].y-player.y)<9){arr.splice(i,1);fn();}\n}\n\n/* ---------- update ---------- */\nfunction updateInputMovement(dt){\n  const mv=getMoveVector(),sp=player.speeds[player.speedLevel];\n  player.x=clamp(player.x+mv.x*sp*dt,12,BASE_W-12);player.y=clamp(player.y+mv.y*sp*dt,10,BASE_H-10);\n}\nfunction updatePlaying(dt){\n  frameCount+=dt;updateAmb(dt);\n  updateInputMovement(dt);updateTrail();tryPlayerFire(dt);\n  if(player.invuln>0)player.invuln-=dt;\n  if(!boss){\n    stageTime+=dt*16.6667;spawnTimer-=dt*16.6667;\n    if(spawnTimer<=0){spawnWave();spawnTimer=cfgCurrent.spawnInterval;}\n    if(stageTime>=cfgCurrent.duration)startBossFight();\n  }\n  updateBullets(dt);updateEBullets(dt);updateEnemies(dt);updateParticles(dt);updateItems(dt);\n  if(boss&&!bossDying)updateBoss(dt);\n  handleCollisions();\n  if(bossDying){\n    bossDeathTimer-=dt;\n    if(Math.random()<.35){boom(boss.x+rand(-boss.w/2,boss.w/2),boss.y+rand(-boss.h/2,boss.h/2),rand(10,22));playTone(rand(80,160),.1,\'sawtooth\',.06);}\n    if(bossDeathTimer<=0){boom(boss.x,boss.y,70);finishBoss();}\n  }\n}\nfunction update(dt){\n  if(shakeTimer>0)shakeTimer-=dt;\n  switch(state){\n    case \'PLAYING\':updatePlaying(dt);break;\n    case \'BOSSINTRO\':frameCount+=dt;updateAmb(dt);updateParticles(dt);if(boss&&boss.entryTimer>0)boss.x-=.9*dt;if(boss&&boss.x<=boss.hx)boss.entryTimer=0;bossIntroTimer-=dt;if(bossIntroTimer<=0){boss.entryTimer=0;boss.x=boss.hx;state=\'PLAYING\';}break;\n    case \'STAGECLEAR\':stageClearTimer-=dt*16.6667;if(stageClearTimer<=0){if(stageIndex>=8){state=\'ENDING\';showEnding();}else enterShop();}break;\n    default:updateAmb(dt);\n  }\n}\n\n/* ---------- background ---------- */\nconst TT=[0,1,1,2,1,0,2,0];let bgN=0,BG={},amb=[];\nfunction buildBG(n){\n  bgN=n;const th=STAGE_COLORS[n-1],far=cv(768,216),g=far.getContext(\'2d\');\n  const gr=g.createLinearGradient(0,0,0,216);gr.addColorStop(0,th.sky1);gr.addColorStop(1,th.sky2);g.fillStyle=gr;g.fillRect(0,0,768,216);\n  let sd=n*77+5;const rn=()=>(sd=(sd*16807)%2147483647)/2147483647;\n  for(let i=0;i<16;i++){const x=rn()*768,y=rn()*216,r=40+rn()*70;\n    for(const o of [0,-768]){const q=g.createRadialGradient(x+o,y,0,x+o,y,r);q.addColorStop(0,hx(th.accent,.14));q.addColorStop(1,hx(th.accent,0));g.fillStyle=q;g.fillRect(x+o-r,y-r,r*2,r*2);}}\n  if([1,3,6,8].includes(n)){const x=200+rn()*300,y=50+rn()*110,r=30+rn()*20,q=g.createRadialGradient(x-r*.4,y-r*.4,2,x,y,r);\n    q.addColorStop(0,shade(th.accent,.7));q.addColorStop(1,\'#04060c\');g.fillStyle=q;g.beginPath();g.arc(x,y,r,0,7);g.fill();\n    g.strokeStyle=hx(th.accent,.45);g.lineWidth=2;g.beginPath();g.ellipse(x,y,r*1.7,r*.35,-.3,0,7);g.stroke();}\n  if(n==2){const q=g.createLinearGradient(0,120,0,216);q.addColorStop(0,\'rgba(255,90,20,0)\');q.addColorStop(1,\'rgba(255,90,20,.35)\');g.fillStyle=q;g.fillRect(0,120,768,96);}\n  if(n==4||n==7){g.fillStyle=\'rgba(0,0,0,.28)\';for(let i=0;i<14;i++){g.fillRect(i*55+rn()*20,0,10+rn()*14,216);}g.fillStyle=hx(th.accent,.08);for(let y=20;y<216;y+=28)g.fillRect(0,y,768,1);}\n  if(n==8){g.strokeStyle=hx(\'#ffffff\',.08);for(let r=20;r<260;r+=26){g.beginPath();g.arc(384,108,r,0,7);g.stroke();}}\n  BG.far=far;\n  const st=cv(768,216),s=st.getContext(\'2d\'),T=TT[n-1];\n  if(T){const hgt=x=>T==1?14+9*Math.sin(x*6.2832*3/768)+7*Math.sin(x*6.2832*8/768+2):12+((Math.floor(x/24)*7919+n*13)%5)*4;\n    for(const top of [1,0]){s.beginPath();s.moveTo(0,top?0:216);for(let x=0;x<=768;x+=T==1?4:24){const h=hgt(x);s.lineTo(x,top?h:216-h);if(T==2)s.lineTo(x+24,top?h:216-h);}s.lineTo(768,top?0:216);s.closePath();\n      s.fillStyle=hx(th.sky1,.92);s.fill();s.strokeStyle=hx(th.accent,.55);s.lineWidth=1.5;s.stroke();}}\n  BG.ter=st;amb=[];for(let i=0;i<34;i++)amb.push({x:rand(0,BASE_W),y:rand(0,BASE_H),s:rand(.5,1.8),a:rand(.2,.7)});\n}\nfunction updateAmb(dt){\n  starLayers.forEach((L,li)=>L.forEach(s=>{s.x-=(.3+li*.5)*dt;if(s.x<0){s.x=BASE_W;s.y=rand(0,BASE_H);}}));\n  const vy=[0,-.25,.3,0,.15,0,0,0][stageIndex-1]||0;\n  amb.forEach(p=>{p.x-=(p.s*1.4+1)*dt;p.y+=vy*p.s*dt+Math.sin(frameCount*.03+p.s*9)*.1;if(p.x<-3){p.x=BASE_W+3;p.y=rand(0,BASE_H);}if(p.y<-3)p.y=BASE_H+3;if(p.y>BASE_H+3)p.y=-3;});\n}\nconst starLayers=[[],[],[]];for(let li=0;li<3;li++)for(let i=0;i<40;i++)starLayers[li].push({x:rand(0,BASE_W),y:rand(0,BASE_H),s:li+1});\nfunction drawBG(theme){\n  if(bgN!==stageIndex)buildBG(stageIndex);\n  const fx=(frameCount*.15)%768;ctx.drawImage(BG.far,-fx,0);ctx.drawImage(BG.far,768-fx,0);\n  starLayers.forEach((L,li)=>{L.forEach((s,k)=>{ctx.globalAlpha=(.3+li*.25)*(.7+.3*Math.sin(frameCount*.05+k));ctx.fillStyle=li===2?theme.accent:\'#fff\';ctx.fillRect(Math.floor(s.x),Math.floor(s.y),s.s,s.s);});});\n  ctx.globalAlpha=1;\n  amb.forEach(p=>{ctx.globalAlpha=p.a;ctx.fillStyle=theme.accent;ctx.fillRect(Math.floor(p.x),Math.floor(p.y),p.s>1.2?2:1,1);});ctx.globalAlpha=1;\n  if(TT[stageIndex-1]){const tx=(frameCount*.9)%768;ctx.drawImage(BG.ter,-tx,0);ctx.drawImage(BG.ter,768-tx,0);}\n}\n\n/* ---------- drawing ---------- */\nfunction drawPlayerShip(){\n  if(player.invuln>0&&Math.floor(player.invuln/4)%2===0)return;\n  const x=player.x,y=player.y,fl=rand(3,7);\n  gl(\'rgba(255,150,40,.8)\',11,x-13,y,.8);ctx.fillStyle=\'#ffb347\';ctx.fillRect(Math.round(x-15-fl),Math.round(y)-1,fl+2,2);ctx.fillStyle=\'#fff6c8\';ctx.fillRect(Math.round(x-14-fl/2),Math.round(y),fl/2+2,1);\n  spr(PS,x,y);gl(\'rgba(90,200,255,.6)\',8,x+3,y,.7);\n  if(player.barrierCharges>0){\n    const a=player.barrierCharges<2&&Math.floor(frameCount/5)%2?.4:1,g=ctx.createRadialGradient(x,y,6,x,y,15);\n    g.addColorStop(0,\'rgba(120,240,255,0)\');g.addColorStop(1,\'rgba(120,240,255,.45)\');ctx.globalAlpha=a;ctx.fillStyle=g;ctx.beginPath();ctx.arc(x,y,15,0,7);ctx.fill();\n    ctx.strokeStyle=\'#bffaff\';ctx.lineWidth=1;ctx.beginPath();ctx.arc(x,y,14+Math.sin(frameCount*.2),0,7);ctx.stroke();ctx.globalAlpha=1;\n  }\n  for(let i=0;i<player.options;i++){const p=getOptionPos(i);gl(\'rgba(255,220,100,.8)\',9,p.x,p.y,.9);\n    ctx.fillStyle=\'#070912\';ctx.beginPath();ctx.arc(p.x,p.y,4,0,7);ctx.fill();ctx.fillStyle=\'#ffc93c\';ctx.beginPath();ctx.arc(p.x,p.y,3,0,7);ctx.fill();ctx.fillStyle=\'#fff\';ctx.fillRect(Math.round(p.x)-1,Math.round(p.y)-1,2,2);}\n}\nfunction drawBullets(){\n  bullets.forEach(b=>{\n    const x=Math.round(b.x),y=Math.round(b.y);\n    if(b.type===\'laser\'){gl(\'rgba(60,220,255,.8)\',12,b.x,b.y,.8);ctx.fillStyle=\'#1fb8ff\';ctx.fillRect(x-8,y-2,16,4);ctx.fillStyle=\'#bff6ff\';ctx.fillRect(x-8,y-1,16,2);ctx.fillStyle=\'#fff\';ctx.fillRect(x-6,y,12,1);}\n    else if(b.type===\'ripple\'){ctx.strokeStyle=\'#4aa8ff\';ctx.lineWidth=2.5;ctx.beginPath();ctx.ellipse(x,y,3+(b.h-14)*.1,b.h/2,0,-1.2,1.2);ctx.stroke();ctx.strokeStyle=\'#d8f4ff\';ctx.lineWidth=1;ctx.stroke();gl(\'rgba(80,170,255,.5)\',9,x,y,.6);}\n    else if(b.type===\'missile\'){gl(\'rgba(255,230,120,.7)\',8,b.x,b.y,.8);ctx.fillStyle=\'#070912\';ctx.fillRect(x-4,y-2,9,4);ctx.fillStyle=\'#ffe97a\';ctx.fillRect(x-3,y-1,7,2);ctx.fillStyle=\'#fff\';ctx.fillRect(x+2,y-1,2,2);}\n    else{gl(\'rgba(120,255,90,.8)\',9,b.x,b.y,.8);ctx.fillStyle=\'#1c6b14\';ctx.fillRect(x-4,y-2,9,4);ctx.fillStyle=\'#a6ff5a\';ctx.fillRect(x-3,y-1,7,2);ctx.fillStyle=\'#fff\';ctx.fillRect(x-1,y-1,4,1);}\n  });\n}\nfunction drawEBullets(){\n  eBullets.forEach(b=>{\n    gl(EBG[b.k],b.k>1?11:8,b.x,b.y,.55+.25*Math.sin(frameCount*.3));\n    if(b.k===1){ctx.save();ctx.translate(Math.round(b.x),Math.round(b.y));ctx.rotate(Math.atan2(b.vy,b.vx));ctx.drawImage(EB[1],-7,-6);ctx.restore();}\n    else spr(EB[b.k],b.x,b.y);\n  });\n}\nfunction drawEnemies(){\n  enemies.forEach(e=>{\n    const im=e.data.img;ctx.save();\n    if(e.type===\'phantom\')ctx.globalAlpha=.3+.7*(e.al||1);\n    if(e.type===\'sniper\'&&e.ch>0){ctx.globalAlpha=.5+.4*Math.sin(e.ch);ctx.fillStyle=\'#ff5de0\';ctx.fillRect(0,Math.round(e.y),Math.round(e.x),1);ctx.globalAlpha=1;}\n    const dw=im.width*e.drawScale,dh=im.height*e.drawScale,fl=2+Math.floor((frameCount+e.ph*10)%4);\n    gl(\'rgba(160,90,255,.65)\',9,e.x+dw/2,e.y,.75);\n    ctx.fillStyle=\'#a855f7\';ctx.fillRect(Math.round(e.x+dw/2-1),Math.round(e.y)-1,fl+2,2);\n    ctx.fillStyle=\'#e9d5ff\';ctx.fillRect(Math.round(e.x+dw/2-1),Math.round(e.y),Math.max(1,fl),1);\n    ctx.drawImage(im,Math.round(e.x-dw/2),Math.round(e.y-dh/2),dw,dh);\n    if(e.fl>0){ctx.globalAlpha=.7;ctx.drawImage(sil(im),Math.round(e.x-dw/2),Math.round(e.y-dh/2),dw,dh);}\n    if(e.type===\'mine\'&&Math.floor(frameCount/10)%2)gl(\'rgba(255,60,60,.9)\',7,e.x,e.y,.9);\n    ctx.restore();\n    if(e.hv){ctx.fillStyle=\'#000\';ctx.fillRect(Math.round(e.x-10),Math.round(e.y-e.h/2-6),20,3);ctx.fillStyle=\'#ff5d5d\';ctx.fillRect(Math.round(e.x-9),Math.round(e.y-e.h/2-5),18*e.hp/e.maxhp,1);}\n  });\n}\nfunction drawBoss(){\n  const b=boss,im=b.img,sh=b.dash===1?rand(-1.5,1.5):0;\n  ctx.save();ctx.translate(sh,0);\n  gl(hx(b.color,.35),Math.max(im.width,im.height)*.6,b.x,b.y,.5);\n  spr(im,b.x,b.y);\n  if(b.flash>0){ctx.globalAlpha=.65;spr(sil(im),b.x,b.y);ctx.globalAlpha=1;}\n  const p=.7+.3*Math.sin(frameCount*.25);\n  gl(b.rg?\'rgba(255,60,60,.95)\':hx(b.color,.95),16+p*5,b.x-im.width/2+im.core[0],b.y-im.height/2+im.core[1],p);\n  ctx.fillStyle=\'#fff\';ctx.fillRect(Math.round(b.x-im.width/2+im.core[0])-1,Math.round(b.y-im.height/2+im.core[1])-1,3,3);\n  ctx.restore();\n}\nfunction drawItems(){\n  capsules.concat(crystalItems).forEach(c=>{\n    const cap=capsules.includes(c),a=c.st===2&&c.wait<4000&&Math.floor(frameCount/6)%2?.35:1;\n    ctx.globalAlpha=a;gl(cap?\'rgba(70,255,140,.8)\':\'rgba(94,200,255,.8)\',cap?11:9,c.x,c.y,(.6+.3*Math.sin(frameCount*.15))*a);\n    spr(cap?CAP:CRY,c.x,c.y);if(c.mag||c.st===1)gl(\'rgba(255,255,255,.6)\',6,c.x,c.y,.7);ctx.globalAlpha=1;\n  });\n}\nfunction drawParticles(){\n  ctx.globalCompositeOperation=\'lighter\';\n  particles.forEach(p=>{ctx.globalAlpha=Math.max(0,p.life/p.maxlife);ctx.fillStyle=p.color;ctx.fillRect(Math.floor(p.x-p.size/2),Math.floor(p.y-p.size/2),p.size,p.size);});\n  rings.forEach(r=>{ctx.globalAlpha=Math.max(0,r.life);ctx.strokeStyle=\'#ffd27a\';ctx.lineWidth=2;ctx.beginPath();ctx.arc(r.x,r.y,r.r,0,7);ctx.stroke();});\n  ctx.globalAlpha=1;ctx.globalCompositeOperation=\'source-over\';\n}\nfunction updateHUD(){\n  document.getElementById(\'hudScore\').textContent=score;\n  document.getElementById(\'hudLives\').textContent=player.lives;\n  document.getElementById(\'hudContinues\').textContent=continues;\n  document.getElementById(\'hudCrystals\').textContent=crystals;\n  document.getElementById(\'hudStage\').textContent=stageIndex+\'/8\';\n  const hb=document.getElementById(\'hpBar\');hb.classList.toggle(\'low\',player.hp===1);\n  hb.querySelectorAll(\'b\').forEach((el,i)=>el.classList.toggle(\'on\',i<player.hp));\n  for(let i=0;i<7;i++)document.getElementById(\'m\'+i).classList.toggle(\'active\',i===meterIndex);\n  let tag=player.weapon.toUpperCase();\n  if(player.missile)tag+=\' +MIS\';if(player.options)tag+=\' OPT\'+player.options;\n  if(player.barrierCharges>0)tag+=\' BAR\'+player.barrierCharges;tag+=\' SPD\'+player.speedLevel;\n  document.getElementById(\'weaponTag\').textContent=tag;\n  const bw=document.getElementById(\'bossBarWrap\');\n  if(boss){bw.classList.remove(\'hidden\');document.getElementById(\'bossBarFill\').style.width=Math.max(0,boss.hp/boss.maxHp*100)+\'%\';}else bw.classList.add(\'hidden\');\n}\nfunction render(){\n  const theme=cfgCurrent?cfgCurrent.theme:STAGE_COLORS[0];\n  ctx.setTransform(2,0,0,2,0,0);ctx.imageSmoothingEnabled=false;\n  ctx.save();\n  if(shakeTimer>0)ctx.translate(rand(-shakeMag,shakeMag),rand(-shakeMag,shakeMag));\n  drawBG(theme);\n  if(state===\'PLAYING\'||state===\'BOSSINTRO\'||state===\'STAGECLEAR\'){\n    drawItems();drawEnemies();if(boss&&!(bossDying&&Math.floor(bossDeathTimer/3)%2))drawBoss();\n    drawBullets();drawEBullets();if(state!==\'STAGECLEAR\'||!boss)drawPlayerShip();drawParticles();\n    if(!boss){ctx.fillStyle=theme.accent;ctx.globalAlpha=.6;ctx.fillRect(0,BASE_H-1,BASE_W*Math.min(1,stageTime/cfgCurrent.duration),1);ctx.globalAlpha=1;}\n    updateHUD();\n  }\n  ctx.restore();\n}\n\n/* ---------- main loop ---------- */\nlet lastTs=0;\nfunction loop(ts){\n  if(!lastTs) lastTs=ts;\n  const dt=Math.min((ts-lastTs)/16.6667,3);\n  lastTs=ts;\n  if(!pauseState) update(dt);\n  render();\n  requestAnimationFrame(loop);\n}\nrequestAnimationFrame(loop);\nshowScreen(\'screenTitle\');\n})();\n</script>\n</body>\n</html>'

EMBEDDED_WEB_APPS = {
    'music_player.html': MUSIC_PLAYER_HTML,
    'game_hub.html': GAME_HUB_HTML,
    'duck.html': DUCK_HTML,
    'othello.html': OTHELLO_HTML,
    'tictactoe.html': TICTACTOE_HTML,
    'Stellar.html': STELLAR_HTML,
}

def ensure_bundled_webapp_files() -> Path:
    """Ensure music_player.html, game_hub.html, and the 4 games exist on disk (preferring app_dir() or DATA_DIR/WebApps)."""
    target_dir = app_dir()
    try:
        probe = target_dir / '.webapp_write_probe'
        probe.write_text('ok', encoding='utf-8')
        probe.unlink()
    except OSError:
        target_dir = DATA_DIR / 'WebApps'
        target_dir.mkdir(parents=True, exist_ok=True)
    for filename, html_text in EMBEDDED_WEB_APPS.items():
        fpath = target_dir / filename
        if not fpath.is_file():
            try:
                fpath.write_text(html_text, encoding='utf-8')
            except OSError:
                pass
    return target_dir

class Config:
    def __init__(self, path: Path):
        self.path = path
        self.data = dict(DEFAULTS)
        stored = read_json(path, {})
        if isinstance(stored, dict):
            self.data.update({k: v for k, v in stored.items() if k in DEFAULTS})
        # Previous Neutron versions enabled AdBlock by default. Require an explicit
        # opt-in once after upgrade, rather than silently carrying that default forward.
        if not bool(self.data.get("adblock_opt_in_acknowledged", False)):
            self.data["adblock_enabled"] = False
            self.data["adblock_opt_in_acknowledged"] = True

    def __getitem__(self, k):
        return self.data[k]

    def __setitem__(self, k, v):
        self.data[k] = v

    def save(self):
        write_json(self.path, self.data)


# ============================================================
# 2) Helpers: URL, fonts, theme
# ============================================================
_SCHEME_RE = re.compile(r"^[a-zA-Z][a-zA-Z0-9+.\-]*:")
_HOSTPORT_RE = re.compile(r"^[^\s:/]+:\d+")
_DOMAIN_RE = re.compile(r"^(localhost|(\d{1,3}\.){3}\d{1,3}|\[[0-9a-fA-F:]+\]|([^\s./:]+\.)+[^\s./:]{2,})(:\d+)?([/?#]\S*)?$")
_OK_SCHEMES = ("http", "https", "file", "view-source", "about", "chrome", "devtools", "data", "blob", "ftp", "neutron")


def smart_url(text: str, cfg: Config) -> QUrl:
    t = text.strip()
    if not t:
        return QUrl("about:blank")
    if re.match(r"^[a-zA-Z]:[\\/]", t):
        return QUrl.fromLocalFile(t)
    if _SCHEME_RE.match(t) and not _HOSTPORT_RE.match(t):
        if t.split(":", 1)[0].lower() in _OK_SCHEMES:
            return QUrl.fromUserInput(t)
    elif _DOMAIN_RE.match(t):
        local = t.startswith(("localhost", "127.", "192.168.", "10."))
        return QUrl(("http://" if local else "https://") + t)
    tpl = SEARCH_ENGINES.get(cfg["search_engine"], SEARCH_ENGINES["Google"])
    return QUrl(tpl.replace("{}", QUrl.toPercentEncoding(t).data().decode()))


def origin_of(url: QUrl) -> str:
    if url.scheme() not in ("http", "https") or not url.host():
        return ""
    port = url.port()
    default = 443 if url.scheme() == "https" else 80
    return f"{url.scheme()}://{url.host()}" + (f":{port}" if port not in (-1, default) else "")


_FONT_FAMILIES = None


def pick_font(candidates) -> str:
    global _FONT_FAMILIES
    if _FONT_FAMILIES is None:
        try:
            _FONT_FAMILIES = set(QFontDatabase.families())
        except Exception:
            log.exception("font enumeration failed")
            _FONT_FAMILIES = set()
    for candidate in candidates:
        if candidate in _FONT_FAMILIES:
            return candidate
    return ""


THAI_SANS = ["Leelawadee UI", "Noto Sans Thai", "Sarabun", "Tahoma", "Segoe UI", "Arial Unicode MS"]
THAI_SERIF = ["TH Sarabun New", "Noto Serif Thai", "Angsana New", "Cordia New", "Times New Roman"]
FIXED_FONTS = ["Cascadia Mono", "Consolas", "Noto Sans Mono", "Courier New"]

PALETTES = {
    "dark": dict(bg="#16181d", surface="#22252d", surface2="#2c303a", text="#eceff4", muted="#9aa3b5", accent="#6d8dff", border="#343946"),
    "light": dict(bg="#e9ecf3", surface="#ffffff", surface2="#eef0f6", text="#1d2030", muted="#667085", accent="#3b5bfd", border="#d3d8e4"),
    "incognito": dict(bg="#120d1a", surface="#1e1628", surface2="#2a1f38", text="#efe9f7", muted="#a99bbd", accent="#b26bff", border="#3a2c4d"),
}
QSS = Template(r"""
QWidget { color: $text; font-size: 13px; }
QMainWindow, QDialog, QMessageBox, QInputDialog { background: $bg; }
QWidget#chrome { background: $bg; }
QWidget#navbar, QWidget#bmbar, QWidget#findbar { background: $surface; border-bottom: 1px solid $border; }
QToolButton { background: transparent; border: none; border-radius: 8px; padding: 4px 8px; }
QToolButton:hover { background: $surface2; }
QToolButton:pressed { background: $border; }
QToolButton:disabled { color: $border; }
QToolButton#nav { font-size: 18px; min-width: 30px; min-height: 30px; font-family: "Segoe UI Symbol","Segoe UI","Noto Sans Symbols2"; }
QToolButton#menuBtn::menu-indicator { image: none; }
QToolButton#tabclose { font-size: 10px; padding: 2px 5px; border-radius: 9px; color: $muted; }
QToolButton#star { font-size: 16px; color: $accent; padding: 2px 6px; }
QFrame#urlframe { background: $bg; border: 1px solid $border; border-radius: 17px; }
QFrame#urlframe:hover { border-color: $accent; }
QLineEdit#urlbar { background: transparent; border: none; font-size: 14px; padding: 6px 2px; }
QLabel#badge { background: $surface2; border: 1px solid $accent; border-radius: 10px; padding: 2px 10px; color: $accent; }
QLineEdit, QPlainTextEdit, QComboBox, QSpinBox { background: $surface2; border: 1px solid $border; border-radius: 6px; padding: 5px 8px; selection-background-color: $accent; }
QPushButton { background: $surface2; border: 1px solid $border; border-radius: 8px; padding: 6px 14px; }
QPushButton:hover { border-color: $accent; }
QPushButton#go { background: $accent; border: none; color: white; font-weight: 600; padding: 6px 16px; border-radius: 15px; }
QTabBar { background: $bg; qproperty-drawBase: 0; }
QTabBar::tab { background: transparent; color: $muted; padding: 8px 10px; margin: 6px 1px 0 1px; min-width: 110px; max-width: 200px; border-top-left-radius: 10px; border-top-right-radius: 10px; }
QTabBar::tab:selected { background: $surface; color: $text; }
QTabBar::tab:hover:!selected { background: $surface2; }
QProgressBar#progress { background: transparent; border: none; min-height: 3px; max-height: 3px; }
QProgressBar#progress::chunk { background: $accent; }
QStatusBar { background: $bg; color: $muted; }
QMenu { background: $surface; border: 1px solid $border; border-radius: 8px; padding: 6px; }
QMenu::item { padding: 7px 28px 7px 18px; border-radius: 5px; }
QMenu::item:selected { background: $accent; color: white; }
QMenu::separator { height: 1px; background: $border; margin: 5px 8px; }
QTableWidget { background: $surface; border: 1px solid $border; gridline-color: $border; }
QTableWidget::item:selected { background: $accent; color: white; }
QHeaderView::section { background: $surface2; border: none; padding: 6px; }
QTabWidget::pane { border: 1px solid $border; border-radius: 6px; }
QScrollBar:vertical { background: transparent; width: 10px; }
QScrollBar::handle:vertical { background: $border; border-radius: 5px; min-height: 30px; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QToolTip { background: $surface; color: $text; border: 1px solid $border; padding: 4px; }
QSplitter::handle { background: $border; }
""")


def build_qss(theme: str) -> str:
    return QSS.substitute(PALETTES.get(theme, PALETTES["dark"]))


# ============================================================
# 3) Storage: history / bookmarks / password vault / session
# ============================================================
class HistoryDB:
    def __init__(self, path: Path):
        self.conn = sqlite3.connect(str(path), isolation_level=None, check_same_thread=False)
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.execute("PRAGMA synchronous=NORMAL")
        self.conn.execute("PRAGMA busy_timeout=4000")
        self.conn.execute("CREATE TABLE IF NOT EXISTS history (id INTEGER PRIMARY KEY AUTOINCREMENT, url TEXT NOT NULL, title TEXT, visited REAL NOT NULL)")
        self.conn.execute("CREATE INDEX IF NOT EXISTS idx_hist_v ON history(visited DESC)")
        self._last = ("", 0.0)
        self._lock = threading.RLock()

    def add(self, url: str, title: str):
        now = time.time()
        with self._lock:
            if self._last[0] == url and now - self._last[1] < 5:
                return
            self._last = (url, now)
            try:
                self.conn.execute("INSERT INTO history(url,title,visited) VALUES(?,?,?)", (url, title, now))
            except sqlite3.Error:
                log.exception("history add")

    def search(self, q: str = "", limit: int = 1000):
        try:
            like = f"%{q}%"
            with self._lock:
                return self.conn.execute("SELECT id,title,url,visited FROM history WHERE url LIKE ? OR title LIKE ? ORDER BY visited DESC LIMIT ?", (like, like, limit)).fetchall()
        except sqlite3.Error:
            log.exception("history search")
            return []

    def recent_urls(self, limit: int = 400):
        """Build autocomplete from a bounded recent window, not the full history table."""
        try:
            with self._lock:
                rows = self.conn.execute(
                    "SELECT url, MAX(id) AS last_id FROM "
                    "(SELECT id,url FROM history ORDER BY id DESC LIMIT 3000) "
                    "GROUP BY url ORDER BY last_id DESC LIMIT ?", (limit,)
                ).fetchall()
            return [row[0] for row in rows]
        except sqlite3.Error:
            log.exception("history recent_urls")
            return []

    def delete(self, ids):
        try:
            with self._lock:
                self.conn.executemany("DELETE FROM history WHERE id=?", [(i,) for i in ids])
        except sqlite3.Error:
            log.exception("history delete")

    def clear(self):
        try:
            with self._lock:
                self.conn.execute("DELETE FROM history")
        except sqlite3.Error:
            log.exception("history clear")

    def close(self):
        try:
            with self._lock:
                self.conn.close()
        except sqlite3.Error:
            log.exception("history close")

class Bookmarks(QObject):
    changed = pyqtSignal()

    def __init__(self, path: Optional[Path]):
        super().__init__()
        self.path = path
        self.items: list[dict] = read_json(path, []) if path else []
        if not isinstance(self.items, list):
            self.items = []

    def _save(self):
        if self.path:
            write_json(self.path, self.items)
        self.changed.emit()

    def contains(self, url: str) -> bool:
        return any(b["url"] == url for b in self.items)

    def add(self, title: str, url: str):
        if not self.contains(url):
            self.items.append({"title": title or url, "url": url})
            self._save()

    def remove(self, url: str):
        self.items = [b for b in self.items if b["url"] != url]
        self._save()

    def toggle(self, title: str, url: str):
        self.remove(url) if self.contains(url) else self.add(title, url)


class PasswordVault(QObject):
    """Encrypted password vault. Legacy PBKDF2 vaults migrate to Scrypt on unlock."""
    KDF_SCRYPT = "scrypt"
    SCRYPT_N = 2 ** 17
    SCRYPT_R = 8
    SCRYPT_P = 1
    MIN_MASTER_LENGTH = 12

    def __init__(self, path: Optional[Path]):
        super().__init__()
        self.path = path
        self.data = {"version": 2, "kdf": self.KDF_SCRYPT, "salt": "", "verify": "", "entries": []}
        self._f = None
        self.prompted = False
        self.legacy_unlocked_data = None
        self._last_access = 0.0
        if path:
            d = read_json(path, None)
            if isinstance(d, dict) and "entries" in d:
                self.data = d

    def available(self) -> bool:
        return HAS_CRYPTO and self.path is not None

    def exists(self) -> bool:
        return bool(self.data.get("salt"))

    def unlocked(self) -> bool:
        return self._f is not None

    def touch(self):
        self._last_access = time.time()

    def lock(self):
        self._f = None
        self.legacy_unlocked_data = None
        self._last_access = 0.0

    def _derive(self, pw: str, salt: bytes, kdf_name: str = "scrypt"):
        if kdf_name == "pbkdf2":
            kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=390_000)
        else:
            kdf = Scrypt(salt=salt, length=32, n=self.SCRYPT_N, r=self.SCRYPT_R, p=self.SCRYPT_P)
        return Fernet(base64.urlsafe_b64encode(kdf.derive(pw.encode("utf-8"))))

    def _persist_data(self, data):
        """Atomically persist an encrypted vault; propagate failures to avoid false success."""
        if not self.path:
            raise ValueError("Vault storage is unavailable")
        self.path.parent.mkdir(parents=True, exist_ok=True)
        temporary = self.path.with_name(self.path.name + "." + uuid.uuid4().hex + ".tmp")
        try:
            with temporary.open("w", encoding="utf-8") as handle:
                json.dump(data, handle, ensure_ascii=False, indent=2)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, self.path)
        finally:
            try:
                temporary.unlink(missing_ok=True)
            except OSError:
                pass

    def _save(self):
        if self.path:
            self._persist_data(self.data)

    def _decrypt_entries(self, cipher):
        result = []
        for entry in self.data.get("entries", []):
            try:
                item = json.loads(cipher.decrypt(entry["data"].encode("ascii")).decode("utf-8"))
                result.append({"origin": entry["origin"], "item": item})
            except Exception as exc:
                raise ValueError("Vault entry cannot be decrypted; migration aborted") from exc
        return result

    def _write_scrypt_vault(self, master: str, plain_entries=None):
        salt = os.urandom(16)
        cipher = self._derive(master, salt, self.KDF_SCRYPT)
        entries = []
        for record in (plain_entries or []):
            payload = {"o": record["origin"], **record["item"]}
            entries.append({"data": cipher.encrypt(json.dumps(payload, ensure_ascii=False).encode("utf-8")).decode("ascii")})
        new_data = {
            "version": 2, "kdf": self.KDF_SCRYPT,
            "scrypt": {"n": self.SCRYPT_N, "r": self.SCRYPT_R, "p": self.SCRYPT_P},
            "salt": base64.b64encode(salt).decode("ascii"),
            "verify": cipher.encrypt(b"neutron-vault-v2").decode("ascii"),
            "entries": entries,
        }
        # Write the complete new vault before replacing the in-memory state/key.
        # A failed write therefore leaves the old on-disk vault intact.
        self._persist_data(new_data)
        self.data = new_data
        self._f = cipher
        self.touch()

    def create(self, pw: str):
        if len(pw) < self.MIN_MASTER_LENGTH:
            raise ValueError("Master password must contain at least 12 characters.")
        self._write_scrypt_vault(pw, [])

    def unlock(self, pw: str) -> bool:
        # A failed unlock must never leave a previously-held encryption key active.
        self.lock()
        try:
            salt = base64.b64decode(self.data["salt"], validate=True)
            if len(salt) != 16:
                return False
            kdf_name = self.data.get("kdf", "pbkdf2")
            if kdf_name not in ("pbkdf2", self.KDF_SCRYPT):
                return False
            cipher = self._derive(pw, salt, kdf_name)
            expected = b"neutron-vault-v2" if kdf_name == self.KDF_SCRYPT else b"neutron"
            if cipher.decrypt(self.data["verify"].encode("ascii")) != expected:
                return False
            self._f = cipher
            self.touch()
            if kdf_name != self.KDF_SCRYPT:
                # Decrypt all legacy entries first. Never overwrite until every entry is readable.
                self.legacy_unlocked_data = self._decrypt_entries(cipher)
            return True
        except (InvalidToken, ValueError, KeyError, TypeError, OSError):
            self.lock()
            return False

    def migrate_legacy(self, new_master: str):
        if not self.unlocked() or self.legacy_unlocked_data is None:
            return False
        if len(new_master) < self.MIN_MASTER_LENGTH:
            raise ValueError("Master password must contain at least 12 characters.")
        records = self.legacy_unlocked_data
        self._write_scrypt_vault(new_master, records)
        self.legacy_unlocked_data = None
        return True

    def origins(self) -> set:
        out = set()
        if not self.unlocked():
            return out
        for entry in self.data.get("entries", []):
            item = self._dec(entry)
            if item and item.get("o"):
                out.add(item["o"])
        return out

    def _dec(self, e):
        if self._f is None:
            return None
        try:
            value = json.loads(self._f.decrypt(e["data"].encode("ascii")).decode("utf-8"))
            self.touch()
            return value
        except (InvalidToken, ValueError, TypeError, KeyError, AttributeError):
            return None

    def find(self, origin: str):
        out = []
        for entry in self.data.get("entries", []):
            item = self._dec(entry)
            if item and item.get("o") == origin:
                out.append({"u": item.get("u", ""), "p": item.get("p", "")})
        return out

    def all(self):
        out = []
        for i, entry in enumerate(self.data.get("entries", [])):
            item = self._dec(entry)
            if item:
                out.append((i, item.get("o", ""), item.get("u", ""), item.get("p", "")))
        return out

    def save_entry(self, origin: str, user: str, pw: str):
        if not self.unlocked():
            raise RuntimeError("Vault is locked")
        token = self._f.encrypt(json.dumps({"o": origin, "u": user, "p": pw}, ensure_ascii=False).encode("utf-8")).decode("ascii")
        self.touch()
        for entry in self.data.get("entries", []):
            item = self._dec(entry)
            if item and item.get("o") == origin and item.get("u") == user:
                entry["data"] = token
                self._save()
                return
        self.data.setdefault("entries", []).append({"data": token})
        self._save()

    def delete(self, idxs):
        if not self.unlocked():
            raise RuntimeError("Vault is locked")
        for i in sorted(set(idxs), reverse=True):
            if 0 <= i < len(self.data.get("entries", [])):
                del self.data["entries"][i]
        self._save()

    def backup(self, path: Path):
        if not self.exists():
            raise ValueError("There is no vault to back up.")
        payload = {"format": "NeutronEncryptedVaultBackup", "format_version": 1, "vault": self.data}
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
        try:
            with tmp.open("w", encoding="utf-8") as handle:
                json.dump(payload, handle, ensure_ascii=False, indent=2)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(tmp, path)
        finally:
            try:
                tmp.unlink(missing_ok=True)
            except OSError:
                pass

    def restore_backup(self, path: Path):
        if path.stat().st_size > 20 * 1024 * 1024:
            raise ValueError("Vault backup exceeds the 20 MB safety limit")
        payload = json.loads(path.read_text(encoding="utf-8"))
        if payload.get("format") != "NeutronEncryptedVaultBackup" or not isinstance(payload.get("vault"), dict):
            raise ValueError("Invalid Neutron vault backup")
        d = payload["vault"]
        if not d.get("salt") or not d.get("verify") or not isinstance(d.get("entries"), list):
            raise ValueError("Backup is incomplete")
        if len(d["entries"]) > 10000:
            raise ValueError("Vault backup has too many entries")
        kdf_name = d.get("kdf", "pbkdf2")
        if kdf_name not in ("pbkdf2", self.KDF_SCRYPT):
            raise ValueError("Unsupported vault key-derivation format")
        salt = base64.b64decode(d["salt"], validate=True)
        if len(salt) != 16 or not isinstance(d["verify"], str) or len(d["verify"]) > 4096:
            raise ValueError("Backup has invalid cryptographic metadata")
        for entry in d["entries"]:
            if not isinstance(entry, dict) or not isinstance(entry.get("data"), str) or len(entry["data"]) > 1024 * 1024:
                raise ValueError("Backup contains an invalid encrypted entry")
        # Persist first; only then change current in-memory vault.
        self._persist_data(d)
        self.data = d
        self._f = None
        self.legacy_unlocked_data = None


class MasterPasswordDialog(QDialog):
    """Create/replace a master password with live strength guidance."""

    def __init__(self, parent, title="Create master password", description="Use at least 12 characters."):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setMinimumWidth(430)
        layout = QVBoxLayout(self)
        note = QLabel(description + "\nA longer passphrase with mixed character types is recommended.")
        note.setWordWrap(True)
        layout.addWidget(note)

        form = QFormLayout()
        self.password = QLineEdit()
        self.password.setEchoMode(QLineEdit.EchoMode.Password)
        self.password.setPlaceholderText("At least 12 characters")
        self.confirm = QLineEdit()
        self.confirm.setEchoMode(QLineEdit.EchoMode.Password)
        self.confirm.setPlaceholderText("Enter the same password again")
        form.addRow("Master password", self.password)
        form.addRow("Confirm password", self.confirm)
        layout.addLayout(form)

        self.strength = QProgressBar()
        self.strength.setRange(0, 4)
        self.strength.setValue(0)
        self.strength.setTextVisible(False)
        self.strength_label = QLabel("Strength: enter a password")
        self.match_label = QLabel(" ")
        layout.addWidget(self.strength_label)
        layout.addWidget(self.strength)
        layout.addWidget(self.match_label)

        buttons = QHBoxLayout()
        buttons.addStretch()
        cancel = QPushButton("Cancel")
        self.ok = QPushButton("Continue")
        self.ok.setObjectName("go")
        self.ok.setEnabled(False)
        cancel.clicked.connect(self.reject)
        self.ok.clicked.connect(self._accept_if_valid)
        buttons.addWidget(cancel)
        buttons.addWidget(self.ok)
        layout.addLayout(buttons)
        self.password.textChanged.connect(self._update_strength)
        self.confirm.textChanged.connect(self._update_strength)

    def _update_strength(self, *_):
        value = self.password.text()
        classes = sum((
            any(c.islower() for c in value),
            any(c.isupper() for c in value),
            any(c.isdigit() for c in value),
            any(not c.isalnum() for c in value),
        ))
        if len(value) < PasswordVault.MIN_MASTER_LENGTH:
            score, label = 0, f"Too short: {len(value)}/{PasswordVault.MIN_MASTER_LENGTH} characters"
        elif len(value) >= 20 and classes >= 3:
            score, label = 4, "Strength: Very strong"
        elif len(value) >= 16 and classes >= 3:
            score, label = 3, "Strength: Strong"
        elif classes >= 3:
            score, label = 2, "Strength: Fair"
        else:
            score, label = 1, "Strength: Minimum length met; consider a more varied passphrase"
        self.strength.setValue(score)
        self.strength_label.setText(label)
        matches = bool(self.confirm.text()) and self.confirm.text() == value
        self.match_label.setText("Passwords match" if matches else ("Passwords do not match" if self.confirm.text() else " "))
        self.ok.setEnabled(len(value) >= PasswordVault.MIN_MASTER_LENGTH and matches)

    def _accept_if_valid(self):
        if len(self.password.text()) < PasswordVault.MIN_MASTER_LENGTH:
            QMessageBox.warning(self, APP_NAME, "Use at least 12 characters.")
            return
        if self.password.text() != self.confirm.text():
            QMessageBox.warning(self, APP_NAME, "Passwords do not match.")
            return
        super().accept()

    def value(self) -> str:
        return self.password.text()


def prompt_master_password(parent, title, description):
    dialog = MasterPasswordDialog(parent, title, description)
    if dialog.exec() == QDialog.DialogCode.Accepted:
        return dialog.value()
    return None


def unlock_vault_ui(parent, vault: Optional[PasswordVault]) -> bool:
    if vault is None or not vault.available():
        QMessageBox.information(parent, APP_NAME, "Password manager is unavailable.\nInstall: pip install cryptography (and not in Incognito).")
        return False
    if vault.unlocked() and vault.legacy_unlocked_data is None:
        return True
    P = QLineEdit.EchoMode.Password
    if vault.exists() and not vault.unlocked():
        for _ in range(3):
            pw, ok = QInputDialog.getText(parent, "Neutron Passwords", "Master password:", P)
            if not ok:
                return False
            if vault.unlock(pw):
                break
            QMessageBox.warning(parent, APP_NAME, "Wrong master password.")
        else:
            return False
    elif not vault.exists():
        pw = prompt_master_password(
            parent, "Create Neutron Password Vault",
            "Create a master password to protect saved website credentials.",
        )
        if pw is None:
            return False
        try:
            vault.create(pw)
        except Exception as exc:
            log.exception("vault create")
            QMessageBox.critical(parent, APP_NAME, f"Could not create Password Vault: {exc}")
            return False
        return True

    # Legacy PBKDF2 vault: migrate only after successful unlock and explicit password policy check.
    if vault.legacy_unlocked_data is not None:
        pw = prompt_master_password(
            parent, "Upgrade Password Vault",
            "Your older PBKDF2 vault was unlocked. Choose a new Scrypt master password.",
        )
        if pw is None:
            vault.lock()
            return False
        try:
            vault.migrate_legacy(pw)
            QMessageBox.information(parent, APP_NAME, "Password Vault upgraded to Scrypt + Fernet. Keep a backup of your new master password.")
        except Exception as exc:
            log.exception("vault migration")
            QMessageBox.critical(parent, APP_NAME, f"Vault migration failed; original vault was retained if the write did not complete.\n{exc}")
            vault.lock()
            return False
    return vault.unlocked()


# ---- JS ที่ฉีดเข้าหน้าเว็บ: จับ form login + เติมรหัสผ่านอัตโนมัติ ----
PWD_PREFIX = "__NEUTRON_PWD__"
CAPTURE_JS = r"""
(function(){
  if (window.__neutronPwd) return; window.__neutronPwd = true;
  var log = console.log.bind(console);
  function grab(form){
    try {
      var pw = form.querySelector('input[type=password]');
      if (!pw || !pw.value) return;
      var user = '';
      var c = form.querySelectorAll('input[type=text],input[type=email],input[type=tel],input:not([type])');
      for (var i=0;i<c.length;i++){
        if (c[i].value && (c[i].compareDocumentPosition(pw) & Node.DOCUMENT_POSITION_FOLLOWING)) user = c[i].value;
      }
      log('__NEUTRON_PWD__' + JSON.stringify({u:user, p:pw.value, o:location.origin}));
    } catch(e) {}
  }
  document.addEventListener('submit', function(e){ grab(e.target); }, true);
  document.addEventListener('click', function(e){
    var b = e.target && e.target.closest ? e.target.closest('button,input[type=submit]') : null;
    if (b) { var f = b.form || b.closest('form'); if (f) grab(f); }
  }, true);
  document.addEventListener('keydown', function(e){
    if (e.key === 'Enter' && e.target && e.target.form) grab(e.target.form);
  }, true);
})();
"""
PROBE_JS = "(function(){var e=document.querySelectorAll('input[type=password]');for(var i=0;i<e.length;i++){if(e[i].offsetParent!==null)return true;}return false;})()"
FILL_JS = r"""
(function(u, p){
  var pws = Array.prototype.filter.call(document.querySelectorAll('input[type=password]'), function(e){ return e.offsetParent !== null; });
  if (!pws.length) return false;
  var pw = pws[0];
  function setv(el, v){
    Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set.call(el, v);
    el.dispatchEvent(new Event('input', {bubbles:true}));
    el.dispatchEvent(new Event('change', {bubbles:true}));
  }
  var scope = pw.form || document;
  var c = scope.querySelectorAll('input[type=text],input[type=email],input[type=tel],input:not([type])');
  var user = null;
  for (var i=0;i<c.length;i++){
    if (c[i].offsetParent !== null && (c[i].compareDocumentPosition(pw) & Node.DOCUMENT_POSITION_FOLLOWING)) user = c[i];
  }
  if (user && u && !user.value) setv(user, u);
  if (!pw.value) setv(pw, p);
  return true;
})(%s, %s);
"""


# ============================================================
# 4) Chrome Extensions (QtWebEngine 6.10+, experimental)
# ============================================================
def read_manifest(d: Path) -> dict:
    m = json.loads((d / "manifest.json").read_text(encoding="utf-8-sig"))
    name = str(m.get("name", d.name))
    if name.startswith("__MSG_"):
        key = name[6:-2].lower()
        for lc in (m.get("default_locale", "en"), "en", "en_US"):
            f = d / "_locales" / lc / "messages.json"
            if f.is_file():
                msgs = read_json(f, {})
                for k, v in msgs.items():
                    if k.lower() == key:
                        name = v.get("message", name)
                break
    return {"name": name, "version": str(m.get("version", "?"))}


class ExtensionManager(QObject):
    def __init__(self, pd: "ProfileData"):
        super().__init__(pd)
        self.dir = (pd.path / "Extensions") if pd.path else None
        self.infos: dict[str, object] = {}
        self.mgr = None
        if self.dir is not None and hasattr(pd.profile, "extensionManager"):
            try:
                self.mgr = pd.profile.extensionManager()
                self.mgr.loadFinished.connect(self._loaded)
            except Exception:
                log.exception("extension manager init")
                self.mgr = None

    @property
    def supported(self) -> bool:
        return self.mgr is not None

    @staticmethod
    def _key(p) -> str:
        return os.path.normcase(os.path.normpath(str(p)))

    def _loaded(self, info):
        try:
            self.infos[self._key(info.path())] = info
            err = getattr(info, "error", lambda: "")()
            if err:
                log.warning("extension load error: %s", err)
                return
            enable = getattr(self.mgr, "setExtensionEnabled", None)
            if callable(enable):
                enable(info, True)
        except Exception:
            log.exception("extension loaded cb")

    def autoload(self):
        """Load extensions gradually so a large profile cannot monopolize startup."""
        if not self.supported or not self.dir or not self.dir.exists():
            return
        try:
            self._autoload_queue = [
                d for d in sorted(self.dir.iterdir())
                if (d / "manifest.json").is_file()
            ]
        except OSError:
            log.exception("list extensions for autoload")
            return
        if not self._autoload_queue:
            return
        self._autoload_timer = QTimer(self)
        self._autoload_timer.setInterval(350)
        self._autoload_timer.timeout.connect(self._autoload_next)
        self._autoload_timer.setSingleShot(True)
        self._autoload_timer.start(1800)

    def _autoload_next(self):
        queue = getattr(self, "_autoload_queue", [])
        if not queue:
            timer = getattr(self, "_autoload_timer", None)
            if timer is not None:
                timer.stop()
            return
        folder = queue.pop(0)
        self._load(folder)
        timer = getattr(self, "_autoload_timer", None)
        if timer is not None and queue:
            timer.start(350)

    def _load(self, d: Path):
        try:
            self.mgr.loadExtension(str(d))
        except Exception:
            log.exception("loadExtension %s", d)

    def _unique_dir(self, base: str) -> Path:
        self.dir.mkdir(parents=True, exist_ok=True)
        d, n = self.dir / safe_name(base), 1
        while d.exists():
            n += 1
            d = self.dir / f"{safe_name(base)}_{n}"
        return d

    def add_dir(self, src: str):
        s = Path(src)
        if not (s / "manifest.json").is_file():
            raise ValueError("manifest.json not found in the selected folder")
        dest = self._unique_dir(s.name)
        shutil.copytree(s, dest)
        self._load(dest)

    def add_file(self, path: str):
        data = Path(path).read_bytes()
        if data[:4] == b"Cr24":  # CRX header
            ver = int.from_bytes(data[4:8], "little")
            if ver == 2:
                off = 16 + int.from_bytes(data[8:12], "little") + int.from_bytes(data[12:16], "little")
            else:
                off = 12 + int.from_bytes(data[8:12], "little")
            data = data[off:]
        dest = self._unique_dir(Path(path).stem)
        try:
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                base = dest.resolve()
                for member in z.infolist():
                    target = (dest / member.filename).resolve()
                    if target != base and base not in target.parents:
                        raise ValueError("Extension package contains an unsafe path")
                z.extractall(dest)
        except Exception:
            shutil.rmtree(dest, ignore_errors=True)
            raise
        if not (dest / "manifest.json").is_file():
            shutil.rmtree(dest, ignore_errors=True)
            raise ValueError("manifest.json not found in the package")
        self._load(dest)

    def remove(self, path: str):
        info = self.infos.pop(self._key(path), None)
        if info is not None and self.mgr:
            try:
                self.mgr.unloadExtension(info)
            except Exception:
                log.exception("unloadExtension")
        shutil.rmtree(path, ignore_errors=True)

    def rows(self):
        out = []
        if not self.dir or not self.dir.exists():
            return out
        for d in sorted(self.dir.iterdir()):
            if not (d / "manifest.json").is_file():
                continue
            try:
                m = read_manifest(d)
            except Exception:
                m = {"name": d.name, "version": "?"}
            info = self.infos.get(self._key(d))
            status = "Not loaded"
            if info is not None:
                try:
                    status = "Loaded" if info.isLoaded() else "Not loaded"
                except Exception:
                    status = "Loaded"
            elif not self.supported:
                status = "Unsupported by this Qt build"
            out.append((str(d), [m["name"], m["version"], status]))
        return out

    def popup_url(self, path: str) -> Optional[QUrl]:
        info = self.infos.get(self._key(path))
        try:
            u = info.actionPopupUrl() if info is not None else None
            return u if u and u.isValid() and not u.isEmpty() else None
        except Exception:
            return None


# ============================================================
# 4.5) Built-in AdGuard-compatible blocking + image tools
# ============================================================
class FilterUpdateThread(QThread):
    completed = pyqtSignal(int, str)

    def __init__(self, destinations, parent=None):
        super().__init__(parent)
        self.destinations = destinations
        self._cancel_event = threading.Event()

    def cancel(self):
        self._cancel_event.set()
        self.requestInterruption()

    def _cancelled(self):
        return self._cancel_event.is_set() or self.isInterruptionRequested()

    def run(self):
        ok, errors = 0, []
        for name, url, path in self.destinations:
            if self._cancelled():
                break
            temporary = None
            try:
                req = urllib.request.Request(
                    url, headers={"User-Agent": "NeutronBrowser/1.4 filter updater"}
                )
                chunks, total = [], 0
                with urllib.request.urlopen(req, timeout=3) as response:
                    while not self._cancelled():
                        chunk = response.read(128 * 1024)
                        if not chunk:
                            break
                        total += len(chunk)
                        if total > 18 * 1024 * 1024:
                            raise ValueError("filter list exceeds 18 MB safety limit")
                        chunks.append(chunk)
                if self._cancelled():
                    break
                data = b"".join(chunks)
                text_data = data.decode("utf-8-sig", errors="replace")
                if "<!doctype html" in text_data[:500].lower() or len(text_data.splitlines()) < 10:
                    raise ValueError("response does not look like a filter list")
                path.parent.mkdir(parents=True, exist_ok=True)
                temporary = path.with_suffix(path.suffix + ".tmp")
                temporary.write_text(text_data, encoding="utf-8")
                if self._cancelled():
                    temporary.unlink(missing_ok=True)
                    break
                os.replace(temporary, path)
                ok += 1
            except Exception as exc:
                if self._cancelled():
                    break
                errors.append(f"{name}: {type(exc).__name__}: {exc}")
                log.exception("AdBlock list update failed: %s", name)
            finally:
                if temporary is not None:
                    try:
                        temporary.unlink(missing_ok=True)
                    except OSError:
                        pass
        if not self._cancelled():
            self.completed.emit(ok, "\n".join(errors))


@lru_cache(maxsize=8192)
def _lazy_filter_regex(pattern: str):
    """Compile uncommon wildcard filters only when they become candidates."""
    return re.compile(pattern, re.IGNORECASE)


def _selector_is_chromium_css(selector: str) -> bool:
    selector = (selector or "").strip()
    if not selector or len(selector) > 800:
        return False
    # AdGuard/uBO extended syntax is not CSS and invalidates a whole CSS rule-list.
    unsupported = ("+js(", "#?#", "#%#", ":has-text(", ":contains(",
                   ":matches-css(", ":matches-attr(", ":xpath(", "script:",
                   ":-abp-", ":-moz-binding", "-abp-has(")
    low = selector.lower()
    return not any(token in low for token in unsupported)


class AdBlockCompileThread(QThread):
    completed = pyqtSignal(object, str)

    def __init__(self, root: Path, custom_path: Path, parent=None):
        super().__init__(parent)
        self.root, self.custom_path = Path(root), Path(custom_path)

    def run(self):
        try:
            lines = [ADBLOCK_BUILTIN]
            for path in sorted(self.root.glob("*.txt")):
                if path.name == "custom_rules.txt":
                    continue
                try:
                    lines.append(path.read_text(encoding="utf-8", errors="replace"))
                except OSError:
                    log.exception("read filter %s", path)
            try:
                lines.append(self.custom_path.read_text(encoding="utf-8", errors="replace"))
            except OSError:
                pass
            if self.isInterruptionRequested():
                return
            snapshot = AdBlockManager.build_snapshot(lines, self.isInterruptionRequested)
            if not self.isInterruptionRequested():
                self.completed.emit(snapshot, "")
        except InterruptedError:
            return
        except Exception as exc:
            log.exception("AdBlock compile worker")
            if not self.isInterruptionRequested():
                self.completed.emit(None, f"{type(exc).__name__}: {exc}")


class AdBlockManager(QObject):
    updateFinished = pyqtSignal(int, str)
    compileFinished = pyqtSignal(bool, str)

    """Indexed, cached AdGuard/ABP subset. The request-interceptor path is deliberately small."""

    def __init__(self, pd):
        super().__init__(pd)
        self.pd = pd
        self.enabled = bool(pd.app.cfg["adblock_enabled"])
        self.blocked_count = 0
        self.recent_blocked = []
        self._lock = threading.RLock()
        self._cache = OrderedDict()
        self._cache_limit = 12000
        self._generation = 0
        self._compile_worker = None
        self._compile_pending = False
        self._closing = False
        self._worker = None
        self._compile_timer = QTimer(self)
        self._compile_timer.setSingleShot(True)
        self._compile_timer.timeout.connect(self._compile_rules)
        self.whitelist = set()
        self.cosmetic = {}
        self.rules = []
        self.exception_rules = []
        self.list_cosmetic = {}
        self.list_cosmetic_exceptions = {}
        self.host_index = {}
        self.generic_index = {}
        self.generic_short_index = {}
        self.generic_fallback = ()
        self.exception_host_index = {}
        self.exception_generic_index = {}
        self.exception_generic_short_index = {}
        self.exception_generic_fallback = ()
        self.engine_name = "Neutron Indexed Python Engine"
        self.root = DATA_DIR / "AdBlock"
        self.root.mkdir(parents=True, exist_ok=True)
        self.custom_path = self.root / "custom_rules.txt"
        self.whitelist_path = (pd.path / "adblock_whitelist.json") if pd.path else None
        self.cosmetic_path = (pd.path / "cosmetic_rules.json") if pd.path else None
        saved_whitelist = read_json(self.whitelist_path, []) if self.whitelist_path else []
        self.whitelist = {str(x).strip().lower() for x in saved_whitelist if isinstance(x, str) and str(x).strip()}
        saved_cosmetic = read_json(self.cosmetic_path, {}) if self.cosmetic_path else {}
        self.cosmetic = {
            str(host).lower(): [str(sel).strip() for sel in selectors
                                if isinstance(sel, str) and _selector_is_chromium_css(sel)]
            for host, selectors in saved_cosmetic.items()
            if isinstance(saved_cosmetic, dict) and isinstance(selectors, list)
        } if isinstance(saved_cosmetic, dict) else {}
        # Install a tiny built-in index immediately. Large lists are compiled and
        # updated only after the user explicitly enables AdBlock.
        self._apply_snapshot(self.build_snapshot([ADBLOCK_BUILTIN]), emit=False)
        if self.enabled:
            self.start_enabled_engine()

    def start_enabled_engine(self):
        if self._closing:
            return
        if self._compile_worker is None and not self._compile_timer.isActive():
            # Let the browser paint/respond before parsing tens of thousands of rules.
            self._compile_timer.start(250)
        list_files = [self.root / (safe_name(name) + ".txt") for name in ADBLOCK_LISTS]
        newest = max((f.stat().st_mtime for f in list_files if f.exists()), default=0)
        if (not newest or time.time() - newest > 7 * 86400) and not getattr(AdBlockManager, "_update_scheduled", False):
            AdBlockManager._update_scheduled = True
            QTimer.singleShot(1800, self._auto_update_lists)

    @staticmethod
    def _build_indexes(rules, should_cancel=None):
        host_index, generic_index, short_index, fallback = {}, {}, {}, []
        for idx, rule in enumerate(rules):
            if idx and idx % 2000 == 0:
                if should_cancel and should_cancel():
                    raise InterruptedError("AdBlock compilation cancelled")
                time.sleep(0)
            host = rule.get("host")
            if host:
                host_index.setdefault(host, []).append(idx)
            else:
                anchor = rule.get("anchor")
                if anchor and len(anchor) >= 5:
                    generic_index.setdefault(anchor[:5], []).append(idx)
                elif anchor and len(anchor) >= 3:
                    short_index.setdefault(anchor[:3], []).append(idx)
                else:
                    fallback.append(idx)
        return (
            {k: tuple(v) for k, v in host_index.items()},
            {k: tuple(v) for k, v in generic_index.items()},
            {k: tuple(v) for k, v in short_index.items()},
            tuple(fallback),
        )

    @classmethod
    def build_snapshot(cls, sources, should_cancel=None):
        rules, exceptions, cosmetic, cosmetic_exceptions = [], [], {}, {}
        seen = set()
        processed = 0
        for source in sources:
            for raw in io.StringIO(source):
                processed += 1
                if processed % 1000 == 0:
                    if should_cancel and should_cancel():
                        raise InterruptedError("AdBlock compilation cancelled")
                    time.sleep(0)  # yield the GIL so GUI/network callbacks can run
                line = raw.strip()
                if not line or line.startswith(("!", "[")) or line in seen:
                    continue
                seen.add(line)
                if line.startswith("@@"):
                    parsed = cls._parse_network_rule(line[2:])
                    if parsed:
                        exceptions.append(parsed)
                    continue
                delimiter = "#@#" if "#@#" in line else ("##" if "##" in line else None)
                if delimiter:
                    domains_text, selector = line.split(delimiter, 1)
                    selector = selector.strip()
                    if not _selector_is_chromium_css(selector):
                        continue
                    domains = [d.strip().lower().lstrip(".") for d in domains_text.split(",") if d.strip()]
                    included = [d for d in domains if not d.startswith("~")]
                    excluded = [d[1:] for d in domains if d.startswith("~") and len(d) > 1]
                    if not included:
                        included = ["*"]
                    target = cosmetic_exceptions if delimiter == "#@#" else cosmetic
                    for domain in included:
                        target.setdefault(domain, []).append(selector)
                    for domain in excluded:
                        cosmetic_exceptions.setdefault(domain, []).append(selector)
                    continue
                parsed = cls._parse_network_rule(line)
                if parsed:
                    rules.append(parsed)

        # Compile wildcard/regex patterns in the background worker, never in the
        # synchronous request-interceptor callback.
        for idx, rule in enumerate(itertools.chain(rules, exceptions)):
            if idx and idx % 1000 == 0:
                if should_cancel and should_cancel():
                    raise InterruptedError("AdBlock compilation cancelled")
                time.sleep(0)
            pattern = rule.get("regex_text")
            if pattern:
                try:
                    rule["regex"] = re.compile(pattern, re.IGNORECASE)
                except re.error:
                    rule["regex"] = None
            else:
                rule["regex"] = None
        hi, gi, gsi, gf = cls._build_indexes(rules, should_cancel)
        ehi, egi, egsi, egf = cls._build_indexes(exceptions, should_cancel)
        return {
            "rules": tuple(rules), "exceptions": tuple(exceptions),
            "host_index": hi, "generic_index": gi, "generic_short_index": gsi,
            "generic_fallback": gf,
            "exception_host_index": ehi, "exception_generic_index": egi,
            "exception_generic_short_index": egsi, "exception_generic_fallback": egf,
            "list_cosmetic": {k: tuple(dict.fromkeys(v)) for k, v in cosmetic.items()},
            "list_cosmetic_exceptions": {k: tuple(dict.fromkeys(v)) for k, v in cosmetic_exceptions.items()},
        }

    @staticmethod
    def _compile_rule_candidates(rules, host_index, generic_index, short_index,
                                 fallback, host, url_lower):
        picked = []
        seen = set()
        for suffix in host_suffixes(host):
            for idx in host_index.get(suffix, ()):
                if idx not in seen:
                    seen.add(idx)
                    picked.append(rules[idx])
        # Long anchors use a selective 5-character index; only short anchors
        # use 3-character buckets. This sharply reduces collisions on common
        # URL fragments such as "ads", "api" and "www".
        for width, index in ((5, generic_index), (3, short_index)):
            last = len(url_lower) - width + 1
            for pos in range(max(0, last)):
                bucket = index.get(url_lower[pos:pos + width])
                if bucket:
                    for idx in bucket:
                        if idx not in seen:
                            seen.add(idx)
                            picked.append(rules[idx])
        for idx in fallback:
            if idx not in seen:
                seen.add(idx)
                picked.append(rules[idx])
        return picked

    def _auto_update_lists(self):
        if self._closing:
            AdBlockManager._update_scheduled = False
            return
        try:
            worker = self.update_lists()
            def finished(_ok, _errors):
                try:
                    self.updateFinished.disconnect(finished)
                except Exception:
                    pass
            self.updateFinished.connect(finished)
            def reset_update_state():
                AdBlockManager._update_scheduled = False
                try:
                    self.updateFinished.disconnect(finished)
                except Exception:
                    pass
            worker.finished.connect(reset_update_state)
            if not worker.isRunning():
                worker.start()
        except Exception:
            AdBlockManager._update_scheduled = False
            log.exception("automatic AdBlock list update")

    def _compile_rules(self):
        if self._closing:
            return
        if self._compile_timer.isActive():
            self._compile_timer.stop()
        if self._compile_worker is not None and self._compile_worker.isRunning():
            self._compile_pending = True
            return
        worker = AdBlockCompileThread(self.root, self.custom_path, self)
        self._compile_worker = worker
        worker.completed.connect(self._compile_completed)
        worker.finished.connect(lambda w=worker: self._compile_worker_finished(w))
        worker.start()

    def _compile_worker_finished(self, worker):
        if self._compile_worker is worker:
            self._compile_worker = None
        worker.deleteLater()
        if self._compile_pending and not self._closing:
            self._compile_pending = False
            QTimer.singleShot(0, self._compile_rules)

    def _compile_completed(self, snapshot, error):
        if snapshot is None:
            self.compileFinished.emit(False, error or "AdBlock compilation failed")
            return
        self._apply_snapshot(snapshot, emit=True)

    def _apply_snapshot(self, snapshot, emit=True):
        with self._lock:
            self.rules = snapshot["rules"]
            self.exception_rules = snapshot["exceptions"]
            self.host_index = snapshot["host_index"]
            self.generic_index = snapshot["generic_index"]
            self.generic_short_index = snapshot["generic_short_index"]
            self.generic_fallback = snapshot["generic_fallback"]
            self.exception_host_index = snapshot["exception_host_index"]
            self.exception_generic_index = snapshot["exception_generic_index"]
            self.exception_generic_short_index = snapshot["exception_generic_short_index"]
            self.exception_generic_fallback = snapshot["exception_generic_fallback"]
            self.list_cosmetic = snapshot["list_cosmetic"]
            self.list_cosmetic_exceptions = snapshot["list_cosmetic_exceptions"]
            self._generation += 1
            self._cache.clear()
        if getattr(self.pd, "adblock", None) is self:
            self.pd.refresh_cosmetic_script()
        for window in list(getattr(self.pd.app, "windows", [])):
            if window.pd is self.pd:
                for i in range(window.stack.count()):
                    tab = window.stack.widget(i)
                    if isinstance(tab, BrowserTab):
                        window.apply_page_tools(tab)
        if emit:
            self.compileFinished.emit(True, "")

    @staticmethod
    def _parse_network_rule(line):
        text, options = (line.rsplit("$", 1) + [""])[:2] if "$" in line else (line, "")
        text = text.strip()
        if not text or text.startswith(("!", "#")):
            return None
        host, path, regex_text, anchor = None, "", None, None
        if text.startswith("||"):
            candidate = re.split(r"[\/^|*]", text[2:], maxsplit=1)[0]
            if candidate and not any(ch in candidate for ch in "*?:"):
                host = candidate.lower().lstrip(".").rstrip(".")
                remainder = text[2 + len(candidate):]
                path = remainder.lstrip("^").rstrip("^").lower()
        if host is None:
            body = text.replace("||", "*").replace("|", "^")
            regex_text = re.escape(body).replace(r"\*", ".*").replace(r"\^", r"(?:[^a-zA-Z0-9_.%-]|$)")
            literal_tokens = re.findall(r"[a-z0-9]{3,}", text.lower())
            anchor = max(literal_tokens, key=len) if literal_tokens else None
            # Avoid useless short/overly-common anchors; those are a bounded fallback bucket.
            if anchor in {"https", "http", "www"}:
                others = [x for x in literal_tokens if x not in {"https", "http", "www"}]
                anchor = max(others, key=len) if others else None
        opts = {x.strip().lower() for x in options.split(",") if x.strip()}
        known = {"script", "image", "stylesheet", "xmlhttprequest", "subdocument", "document",
                 "font", "media", "object", "other", "ping"}
        types = frozenset(x for x in opts if x in known)
        not_types = frozenset(x[1:] for x in opts if x.startswith("~") and x[1:] in known)
        domain_opt = next((x.split("=", 1)[1] for x in opts if x.startswith("domain=")), "")
        include = tuple(x.lower().lstrip(".") for x in domain_opt.split("|") if x and not x.startswith("~"))
        exclude = tuple(x[1:].lower().lstrip(".") for x in domain_opt.split("|") if x.startswith("~") and len(x) > 1)
        return {"line": line, "host": host, "path": path, "regex_text": regex_text, "anchor": anchor,
                "types": types, "not_types": not_types, "domain_include": include,
                "domain_exclude": exclude, "third": "third-party" in opts,
                "first": "~third-party" in opts, "important": "important" in opts}

    @staticmethod
    def _resource_name(value):
        name = getattr(value, "name", None)
        raw = str(name if name is not None else value).lower().replace("resourcetype", "")
        aliases = {
            "resourceimagem": "image", "image": "image", "resourceimage": "image",
            "resourcexhr": "xmlhttprequest", "xhr": "xmlhttprequest",
            "subframe": "subdocument", "resourcesubframe": "subdocument",
            "mainframe": "document", "resourcemainframe": "document",
            "stylesheets": "stylesheet", "fontresource": "font",
        }
        if raw in aliases:
            return aliases[raw]
        for needle, result in (("image", "image"), ("xmlhttprequest", "xmlhttprequest"),
                               ("xhr", "xmlhttprequest"), ("mainframe", "document"),
                               ("subframe", "subdocument"), ("stylesheet", "stylesheet"),
                               ("font", "font"), ("media", "media"), ("script", "script"),
                               ("document", "document"), ("ping", "ping")):
            if needle in raw:
                return result
        return "other"

    @staticmethod
    def _rule_matches(rule, url_lower, host, first_host, resource_type, is_third):
        if rule["types"] and resource_type not in rule["types"]:
            return False
        if rule["not_types"] and resource_type in rule["not_types"]:
            return False
        if rule["third"] and not is_third:
            return False
        if rule["first"] and is_third:
            return False
        includes, excludes = rule["domain_include"], rule["domain_exclude"]
        if includes and not any(first_host == d or first_host.endswith("." + d) for d in includes):
            return False
        if excludes and any(first_host == d or first_host.endswith("." + d) for d in excludes):
            return False
        if rule["host"]:
            domain = rule["host"]
            if host != domain and not host.endswith("." + domain):
                return False
            return not rule["path"] or rule["path"] in url_lower
        compiled = rule.get("regex")
        if compiled is None:
            try:
                compiled = _lazy_filter_regex(rule["regex_text"])
            except re.error:
                return False
        return bool(compiled.search(url_lower))

    def should_block(self, url, first_party, resource_type, request_method="GET", is_main_frame=False):
        if not self.enabled:
            return False
        method = (request_method or "GET").upper()
        if is_main_frame or method not in {"GET", "HEAD"}:
            return False
        url_lower = (url or "").lower()
        first_lower = (first_party or "").lower()
        if not url_lower.startswith(("http://", "https://")) or not first_lower.startswith(("http://", "https://")):
            return False
        host, _ = split_url(url_lower)
        first_host, _ = split_url(first_lower)
        if not host or not first_host:
            return False
        if host in (OCR_HOST, BG_HOST) or first_host in (OCR_HOST, BG_HOST):
            return False
        # Search pages often call shared endpoints for suggestions, result data,
        # and navigation. Bypass blocking for the entire search origin to avoid
        # intermittent freezes and broken result pages; protection remains active
        # on ordinary websites.
        if is_search_engine_host(first_host):
            return False
        rt = self._resource_name(resource_type)
        if rt == "document":
            return False
        with self._lock:
            whitelist = self.whitelist
            generation = self._generation
            cache_key = (generation, url_lower, first_host, rt)
            cached = self._cache.get(cache_key, None)
            if cached is not None:
                self._cache.move_to_end(cache_key)
                if cached:
                    self._record_blocked(host, rt)
                return cached
            rules, exceptions = self.rules, self.exception_rules
            hi, gi, gsi, gf = self.host_index, self.generic_index, self.generic_short_index, self.generic_fallback
            ehi, egi, egsi, egf = (self.exception_host_index, self.exception_generic_index,
                                    self.exception_generic_short_index, self.exception_generic_fallback)
        if any(first_host == h or first_host.endswith("." + h) for h in whitelist):
            return False
        is_third = base_domain(host) != base_domain(first_host)
        exception_candidates = self._compile_rule_candidates(exceptions, ehi, egi, egsi, egf, host, url_lower)
        exception_hit = any(self._rule_matches(r, url_lower, host, first_host, rt, is_third)
                            for r in exception_candidates)
        candidates = self._compile_rule_candidates(rules, hi, gi, gsi, gf, host, url_lower)
        block_hit = False
        important_hit = False
        for rule in candidates:
            if self._rule_matches(rule, url_lower, host, first_host, rt, is_third):
                block_hit = True
                important_hit = bool(rule["important"])
                if important_hit:
                    break
        result = block_hit and (important_hit or not exception_hit)
        with self._lock:
            self._cache[cache_key] = result
            if len(self._cache) > self._cache_limit:
                self._cache.popitem(last=False)
        if result:
            self._record_blocked(host, rt)
        return result

    def _record_blocked(self, host, resource_type):
        try:
            entry = (time.strftime("%H:%M:%S"), str(host or "(unknown host)")[:180], str(resource_type)[:40])
            with self._lock:
                self.blocked_count += 1
                self.recent_blocked.append(entry)
                if len(self.recent_blocked) > 300:
                    del self.recent_blocked[:-300]
        except Exception:
            log.debug("Could not record blocked request", exc_info=True)

    def _persist_user_rules(self):
        if self.whitelist_path:
            write_json(self.whitelist_path, sorted(self.whitelist))
        if self.cosmetic_path:
            write_json(self.cosmetic_path, self.cosmetic)
        self.pd.refresh_cosmetic_script()
        for window in list(getattr(self.pd.app, "windows", [])):
            if window.pd is self.pd:
                for i in range(window.stack.count()):
                    tab = window.stack.widget(i)
                    if isinstance(tab, BrowserTab):
                        window.apply_page_tools(tab)

    def add_whitelist(self, host):
        host = (host or "").strip().lower()
        if not host:
            return
        with self._lock:
            self.whitelist = set(self.whitelist) | {host}
            self._cache.clear()
        self._persist_user_rules()

    def remove_whitelist(self, host):
        host = (host or "").strip().lower()
        with self._lock:
            self.whitelist = set(self.whitelist) - {host}
            self._cache.clear()
        self._persist_user_rules()

    def add_cosmetic(self, host, selector):
        host, selector = (host or "*").strip().lower(), (selector or "").strip()
        if not _selector_is_chromium_css(selector):
            raise ValueError("Selector is empty, too long, or uses unsupported AdGuard extended syntax")
        values = list(self.cosmetic.get(host, []))
        if selector not in values:
            values.append(selector)
        self.cosmetic[host] = values
        self._persist_user_rules()

    def remove_cosmetic(self, host, selector):
        values = self.cosmetic.get(host, [])
        self.cosmetic[host] = [x for x in values if x != selector]
        if not self.cosmetic[host]:
            self.cosmetic.pop(host, None)
        self._persist_user_rules()

    def add_network_rule(self, rule):
        rule = (rule or "").strip()
        if not rule or len(rule) > 2000 or rule.startswith(("!", "[")):
            raise ValueError("Invalid network filter rule")
        parsed = self._parse_network_rule(rule)
        if not parsed:
            raise ValueError("The filter rule is not supported")
        self.custom_path.parent.mkdir(parents=True, exist_ok=True)
        existing = self.custom_path.read_text(encoding="utf-8", errors="replace") if self.custom_path.exists() else ""
        if rule not in existing.splitlines():
            self.custom_path.write_text(existing.rstrip() + "\n" + rule + "\n", encoding="utf-8")
        self._compile_rules()

    def save(self):
        # User settings/cosmetic rules do not require recompiling tens of thousands of network filters.
        self._persist_user_rules()

    def update_lists(self, callback_parent=None):
        if self._closing:
            raise RuntimeError("AdBlock manager is shutting down")
        if self._worker is not None and self._worker.isRunning():
            return self._worker
        destinations = [(name, url, self.root / (safe_name(name) + ".txt")) for name, url in ADBLOCK_LISTS.items()]
        worker = FilterUpdateThread(destinations, self)
        worker.completed.connect(self._update_done)
        worker.finished.connect(worker.deleteLater)
        worker.finished.connect(lambda w=worker: self._filter_worker_finished(w))
        self._worker = worker
        return worker

    def _filter_worker_finished(self, worker):
        if self._worker is worker:
            self._worker = None

    def shutdown(self):
        """Stop background filter work before Qt destroys profile-owned QThreads."""
        self._closing = True
        self._compile_pending = False
        if self._compile_timer.isActive():
            self._compile_timer.stop()
        updater = self._worker
        if updater is not None and updater.isRunning():
            updater.cancel()
            if not updater.wait(7000):
                log.error("AdBlock filter updater did not stop within shutdown timeout")
        compiler = self._compile_worker
        if compiler is not None and compiler.isRunning():
            compiler.requestInterruption()
            if not compiler.wait(6500):
                log.error("AdBlock compiler did not stop within shutdown timeout")

    def _update_done(self, ok, errors):
        if self._closing:
            return
        profiles = list(getattr(self.pd.app, "profiles", {}).values())
        incognito = getattr(self.pd.app, "incognito_pd", None)
        if incognito is not None:
            profiles.append(incognito)
        seen = set()
        for profile_data in profiles:
            if profile_data is None or id(profile_data) in seen:
                continue
            seen.add(id(profile_data))
            try:
                profile_data.adblock._compile_rules()
            except Exception:
                log.exception("AdBlock recompilation failed for profile %s", getattr(profile_data, "name", "?"))
        if id(self.pd) not in seen:
            self._compile_rules()
        log.info("AdBlock lists updated: %s; errors=%s", ok, errors)
        self.updateFinished.emit(ok, errors)

    def rules_count(self):
        with self._lock:
            return len(self.rules)

    def cosmetic_for(self, host):
        """Return only filter-list CSS selectors relevant to this host."""
        host = (host or "").lower().strip(".")
        if is_search_engine_host(host):
            return []
        suffixes = tuple(host_suffixes(host)) if host else ()
        with self._lock:
            out, excluded = [], set()
            for domain in suffixes + ("*",):
                out.extend(self.list_cosmetic.get(domain, ()))
                excluded.update(self.list_cosmetic_exceptions.get(domain, ()))
        return list(dict.fromkeys(x for x in out if x not in excluded and _selector_is_chromium_css(x)))

    def user_cosmetic_for(self, host):
        """Return user-created CSS rules without applying AdGuard list exceptions."""
        host = (host or "").lower().strip(".")
        suffixes = tuple(host_suffixes(host)) if host else ()
        with self._lock:
            values = []
            for domain in suffixes + ("*",):
                values.extend(self.cosmetic.get(domain, ()))
        return list(dict.fromkeys(x for x in values if _selector_is_chromium_css(x)))

    def cosmetic_payload(self):
        with self._lock:
            return {
                "list": {k: list(v) for k, v in self.list_cosmetic.items()},
                "list_exceptions": {k: list(v) for k, v in self.list_cosmetic_exceptions.items()},
                "user": {k: list(v) for k, v in self.cosmetic.items()},
            }


class NeutronRequestInterceptor(QWebEngineUrlRequestInterceptor):
    """Keep this callback cheap: Qt stalls the matching network request until it returns."""
    def __init__(self, manager, parent=None):
        super().__init__(parent)
        self.manager = manager

    def interceptRequest(self, info):
        try:
            url = info.requestUrl().toString()
            first = info.firstPartyUrl().toString()
            resource = info.resourceType()
            name = getattr(resource, "name", str(resource)).lower()
            is_main = "mainframe" in name
            method = bytes(info.requestMethod()).decode("ascii", errors="ignore") or "GET"
            if self.manager.should_block(url, first, resource, method, is_main):
                info.block(True)
        except Exception:
            # Fail open: an adblock exception must never break ordinary navigation.
            log.debug("request interceptor failed open", exc_info=True)


class _SafeImageRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Reject redirects to local/private targets and strip cookies across origins."""
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        target = QUrl(newurl)
        if target.scheme().lower() not in ("http", "https") or not target.host():
            raise urllib.error.HTTPError(newurl, code, "Unsafe redirect target", headers, fp)
        _assert_public_image_host(target.host())
        redirected = super().redirect_request(req, fp, code, msg, headers, newurl)
        if redirected is not None and target.host().lower() != QUrl(req.full_url).host().lower():
            redirected.remove_header("Cookie")
            redirected.remove_header("Authorization")
        return redirected


def _assert_public_image_host(host: str):
    host = (host or "").strip().strip("[]").lower()
    if not host or host == "localhost" or host.endswith(".localhost"):
        raise ValueError("Local image addresses are not allowed")
    try:
        addresses = [ipaddress.ip_address(host)]
    except ValueError:
        addresses = []
        for result in socket.getaddrinfo(host, None, type=socket.SOCK_STREAM):
            try:
                addresses.append(ipaddress.ip_address(result[4][0]))
            except ValueError:
                continue
    if not addresses or any(not addr.is_global for addr in addresses):
        raise ValueError("Image host must resolve only to public IP addresses")


class ImageDownloadThread(QThread):
    progress = pyqtSignal(str)
    completed = pyqtSignal(int, int, str)

    def __init__(self, records, folder, filters, referer, user_agent, cookie_header="", parent=None, max_workers=6):
        super().__init__(parent)
        self.records, self.folder, self.filters = records, Path(folder), filters
        self.referer, self.user_agent, self.cookie_header = referer, user_agent, cookie_header
        self.max_workers = max(1, min(8, int(max_workers)))
        self._cancel_event = threading.Event()

    def cancel(self):
        self._cancel_event.set()
        self.requestInterruption()

    @staticmethod
    def _safe_filename(parsed, mime, index):
        name = unquote(parsed.path()).rsplit("/", 1)[-1] or f"image_{index}"
        name = re.sub(r"[^\w.\-() ]", "_", name, flags=re.UNICODE).strip(" .")[:140] or f"image_{index}"
        if not Path(name).suffix:
            if mime == "image/jpeg": suffix = ".jpg"
            elif mime == "image/png": suffix = ".png"
            elif mime == "image/gif": suffix = ".gif"
            elif mime == "image/webp": suffix = ".webp"
            elif mime == "image/avif": suffix = ".avif"
            elif mime == "image/svg+xml": suffix = ".svg"
            else: suffix = mimetypes.guess_extension(mime) or ".img"
            name += suffix
        return name

    def _download_one(self, index, item, seen_hashes, write_lock):
        if self._cancel_event.is_set() or self.isInterruptionRequested():
            return False, True, "Cancelled"
        url = item.get("url", "")
        parsed = QUrl(url)
        if parsed.scheme().lower() not in ("http", "https"):
            return False, True, "Non-HTTP URL skipped"
        host = parsed.host().lower()
        if not host or parsed.userInfo():
            return False, True, "Invalid URL/authority"
        _assert_public_image_host(host)
        headers = {"User-Agent": self.user_agent, "Referer": self.referer}
        if self.cookie_header and host == QUrl(self.referer).host().lower():
            headers["Cookie"] = self.cookie_header
        opener = urllib.request.build_opener(_SafeImageRedirectHandler())

        # Only pay for a HEAD request when the user actually enabled size filtering.
        min_kb = float(self.filters.get("min_kb", 0) or 0)
        max_kb = float(self.filters.get("max_kb", 0) or 0)
        if min_kb or max_kb:
            try:
                req = urllib.request.Request(url, headers=headers, method="HEAD")
                with opener.open(req, timeout=4) as response:
                    size_hint = int(response.headers.get("Content-Length") or 0) or None
                if size_hint is not None and not self._size_ok(size_hint):
                    return False, True, "Size filter (HEAD)"
            except Exception:
                # HEAD is optional; final GET byte count remains authoritative.
                pass

        req = urllib.request.Request(url, headers=headers)
        chunks, total = [], 0
        with opener.open(req, timeout=7) as response:
            mime = response.headers.get_content_type()
            while not self._cancel_event.is_set() and not self.isInterruptionRequested():
                chunk = response.read(128 * 1024)
                if not chunk:
                    break
                total += len(chunk)
                if total > 50 * 1024 * 1024:
                    return False, True, "Image exceeds 50 MB limit"
                chunks.append(chunk)
        if self._cancel_event.is_set() or self.isInterruptionRequested():
            return False, True, "Cancelled"
        data = b"".join(chunks)
        if len(data) > 50 * 1024 * 1024:
            return False, True, "Image exceeds 50 MB limit"
        if not mime.startswith("image/"):
            known_image = data.startswith((b"\x89PNG\r\n\x1a\n", b"\xff\xd8\xff", b"GIF87a", b"GIF89a", b"RIFF")) or data[:4] in (b"II*\x00", b"MM\x00*")
            if not known_image:
                return False, True, f"Not an image (MIME {mime})"
            if data.startswith(b"\xff\xd8\xff"): mime = "image/jpeg"
            elif data.startswith(b"\x89PNG"): mime = "image/png"
            elif data.startswith((b"GIF87a", b"GIF89a")): mime = "image/gif"
            elif data.startswith(b"RIFF") and data[8:12] == b"WEBP": mime = "image/webp"
        if not self._size_ok(len(data)):
            return False, True, "Size filter (downloaded bytes)"
        digest = hashlib.sha256(data).digest()
        name = self._safe_filename(parsed, mime, index)
        with write_lock:
            if digest in seen_hashes:
                return False, True, "Duplicate image content"
            seen_hashes.add(digest)
            target = self.folder / name
            stem, suffix, n = target.stem, target.suffix, 1
            while target.exists():
                target = self.folder / f"{stem}_{n}{suffix}"
                n += 1
            target.write_bytes(data)
        return True, False, target.name

    def run(self):
        saved = skipped = 0
        errors = []
        try:
            self.folder.mkdir(parents=True, exist_ok=True)
        except OSError as exc:
            self.completed.emit(0, len(self.records), f"Cannot create output folder: {exc}")
            return
        seen_hashes, write_lock = set(), threading.Lock()
        total = len(self.records)
        try:
            with ThreadPoolExecutor(max_workers=min(self.max_workers, max(1, total)), thread_name_prefix="neutron-image") as pool:
                futures = {pool.submit(self._download_one, index, item, seen_hashes, write_lock): (index, item)
                           for index, item in enumerate(self.records, 1)}
                for future in as_completed(futures):
                    index, item = futures[future]
                    try:
                        ok, was_skipped, detail = future.result()
                        if ok:
                            saved += 1
                            self.progress.emit(f"Saved {saved}/{total}: {detail}")
                        elif was_skipped:
                            skipped += 1
                            if detail not in ("Cancelled", "Duplicate image content", "Size filter (HEAD)", "Size filter (downloaded bytes)") and len(errors) < 5:
                                errors.append(f"{item.get('url','')}: {detail}")
                    except Exception as exc:
                        skipped += 1
                        log.exception("image download failed: %s", item.get("url", ""))
                        if len(errors) < 5:
                            errors.append(f"{item.get('url','')}: {type(exc).__name__}: {exc}")
        except Exception as exc:
            log.exception("image download pool failed")
            errors.append(f"Download pool: {type(exc).__name__}: {exc}")
        if self._cancel_event.is_set() or self.isInterruptionRequested():
            errors.append("Download cancelled by user")
        self.completed.emit(saved, skipped, "\n".join(errors))

    def _size_ok(self, size):
        lo, hi = self.filters.get("min_kb", 0), self.filters.get("max_kb", 0)
        kb = size / 1024
        return (not lo or kb >= lo) and (not hi or kb <= hi)


class ImageBatchDialog(QDialog):
    def __init__(self, parent, records):
        super().__init__(parent)
        self.setWindowTitle("Save All Pictures")
        self.resize(960, 620)
        self.records = records
        layout = QVBoxLayout(self)
        form = QHBoxLayout()
        self.min_w, self.max_w = QSpinBox(), QSpinBox()
        self.min_h, self.max_h = QSpinBox(), QSpinBox()
        for w in (self.min_w, self.max_w, self.min_h, self.max_h): w.setRange(0, 100000)
        self.min_kb, self.max_kb = QSpinBox(), QSpinBox()
        for w in (self.min_kb, self.max_kb): w.setRange(0, 1_000_000); w.setSuffix(" KB")
        self.url_filter = QLineEdit(); self.url_filter.setPlaceholderText("URL contains or regex...")
        self.url_regex = QCheckBox("Regex")
        for label, widget in (("Min W", self.min_w), ("Max W", self.max_w), ("Min H", self.min_h), ("Max H", self.max_h),
                              ("Min size", self.min_kb), ("Max size", self.max_kb), ("URL", self.url_filter)):
            form.addWidget(QLabel(label)); form.addWidget(widget)
        form.addWidget(self.url_regex)
        layout.addLayout(form)
        self.table = QTableWidget(0, 4)
        self.table.setHorizontalHeaderLabels(["Save", "Dimensions", "URL", "Alt text"])
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.horizontalHeader().setStretchLastSection(True)
        layout.addWidget(self.table)
        self.count_label = QLabel("")
        layout.addWidget(self.count_label)
        row = QHBoxLayout(); row.addStretch()
        save = QPushButton("Save selected images..."); save.setObjectName("go")
        cancel = QPushButton("Close")
        save.clicked.connect(self.accept); cancel.clicked.connect(self.reject)
        row.addWidget(save); row.addWidget(cancel); layout.addLayout(row)
        for w in (self.min_w, self.max_w, self.min_h, self.max_h, self.min_kb, self.max_kb): w.valueChanged.connect(self.refresh)
        self.url_filter.textChanged.connect(self.refresh)
        self.url_regex.toggled.connect(self.refresh)
        self.refresh()

    def refresh(self):
        self.table.setRowCount(0)
        self.visible_records = []
        q = self.url_filter.text().lower()
        matcher = None
        if q and self.url_regex.isChecked():
            try:
                matcher = re.compile(q, re.IGNORECASE)
            except re.error as exc:
                self.count_label.setText(f"Invalid URL regular expression: {exc}")
                return
        for rec in self.records:
            w, h, url = int(rec.get("width", 0)), int(rec.get("height", 0)), rec.get("url", "")
            if self.min_w.value() and w < self.min_w.value(): continue
            if self.max_w.value() and w > self.max_w.value(): continue
            if self.min_h.value() and h < self.min_h.value(): continue
            if self.max_h.value() and h > self.max_h.value(): continue
            if q and ((matcher.search(url) is None) if matcher else (q not in url.lower())): continue
            if self.min_kb.value() or self.max_kb.value():
                # Real transfer size is checked during download; metadata-only sizes are not reliable.
                pass
            self.visible_records.append(rec)
            r = self.table.rowCount(); self.table.insertRow(r)
            check = QTableWidgetItem(); check.setFlags(check.flags() | Qt.ItemFlag.ItemIsUserCheckable); check.setCheckState(Qt.CheckState.Checked)
            self.table.setItem(r, 0, check)
            self.table.setItem(r, 1, QTableWidgetItem(f"{w} × {h}"))
            self.table.setItem(r, 2, QTableWidgetItem(url))
            self.table.setItem(r, 3, QTableWidgetItem(rec.get("alt", "")))
        self.count_label.setText(f"Showing {len(self.visible_records)} of {len(self.records)} images. File-size filters are checked against downloaded bytes.")

    def accept(self):
        ranges = (
            ("width", self.min_w.value(), self.max_w.value()),
            ("height", self.min_h.value(), self.max_h.value()),
            ("file size", self.min_kb.value(), self.max_kb.value()),
        )
        for label, minimum, maximum in ranges:
            if maximum and minimum and maximum < minimum:
                QMessageBox.warning(self, "Invalid image filter", f"Maximum {label} must be greater than or equal to minimum {label}.")
                return
        super().accept()

    def selected_records(self):
        out = []
        for row, rec in enumerate(self.visible_records):
            if self.table.item(row, 0).checkState() == Qt.CheckState.Checked:
                out.append(rec)
        return out


# ============================================================
# 5) Profiles (Multi-profile + Incognito)
# ============================================================
class ProfileData(QObject):
    def __init__(self, app: "NeutronApp", name: str, incognito: bool = False):
        super().__init__(app.qt)
        self.app, self.name, self.incognito, self.windows = app, name, incognito, 0
        if incognito:
            self.path = None
            self.profile = QWebEngineProfile(self)  # off-the-record: ไม่เขียนลงดิสก์
            self.history, self.bookmarks, self.vault = None, Bookmarks(None), None
        else:
            self.path = PROFILES_DIR / safe_name(name)
            for sub in ("Storage", "Cache"):
                (self.path / sub).mkdir(parents=True, exist_ok=True)
            p = self.profile = QWebEngineProfile(f"neutron-{safe_name(name)}", self)
            p.setPersistentStoragePath(str(self.path / "Storage"))  # cookies / localStorage / IndexedDB
            p.setCachePath(str(self.path / "Cache"))
            p.setPersistentCookiesPolicy(QWebEngineProfile.PersistentCookiesPolicy.ForcePersistentCookies)
            p.setHttpCacheType(QWebEngineProfile.HttpCacheType.DiskHttpCache)
            p.setHttpCacheMaximumSize(300 * 1024 * 1024)
            try:
                self.history = HistoryDB(self.path / "history.db")
            except sqlite3.Error:
                log.exception("history db")
                self.history = None
            self.bookmarks = Bookmarks(self.path / "bookmarks.json")
            self.vault = PasswordVault(self.path / "passwords.vault")
        self.scheme_handler = NeutronSchemeHandler(self)
        self.profile.installUrlSchemeHandler(b"neutron", self.scheme_handler)
        self.profile.downloadRequested.connect(app.downloads.handle)
        self.adblock = AdBlockManager(self)
        self.adblock_interceptor = NeutronRequestInterceptor(self.adblock, self)
        self.profile.setUrlRequestInterceptor(self.adblock_interceptor)
        self.permission_path = (self.path / "permissions.json") if self.path else None
        self.permission_rules = read_json(self.permission_path, {}) if self.permission_path else {}
        self.extensions = ExtensionManager(self)
        self.apply_settings()
        self._inject_scripts()
        QTimer.singleShot(0, self.extensions.autoload)

    def apply_settings(self):
        cfg, s = self.app.cfg, self.profile.settings()
        WA, FF, FS = QWebEngineSettings.WebAttribute, QWebEngineSettings.FontFamily, QWebEngineSettings.FontSize

        def attr(name, val):
            a = getattr(WA, name, None)
            if a is not None:
                s.setAttribute(a, bool(val))

        attr("JavascriptEnabled", cfg["javascript"])
        attr("JavascriptCanOpenWindows", cfg["popups"])
        for n in ("LocalStorageEnabled", "PluginsEnabled", "FullScreenSupportEnabled", "ScrollAnimatorEnabled",
                  "PdfViewerEnabled", "ScreenCaptureEnabled", "JavascriptCanAccessClipboard", "ErrorPageEnabled",
                  "AutoLoadIconsForPage", "WebGLEnabled", "Accelerated2dCanvasEnabled"):
            attr(n, True)
        attr("ForceDarkMode", cfg["force_dark_web"])
        self.profile.setHttpAcceptLanguage(cfg["accept_language"])
        s.setFontFamily(FF.StandardFont, cfg["font_standard"] or pick_font(THAI_SANS))
        s.setFontFamily(FF.SansSerifFont, cfg["font_sans"] or pick_font(THAI_SANS))
        s.setFontFamily(FF.SerifFont, cfg["font_serif"] or pick_font(THAI_SERIF))
        s.setFontFamily(FF.FixedFont, cfg["font_fixed"] or pick_font(FIXED_FONTS))
        s.setFontSize(FS.DefaultFontSize, int(cfg["font_size"]))
        s.setFontSize(FS.DefaultFixedFontSize, int(cfg["font_fixed_size"]))
        s.setFontSize(FS.MinimumFontSize, int(cfg["font_min_size"]))

    def refresh_cosmetic_script(self):
        """Replace only Neutron's own cosmetic script; leave password/userscripts untouched."""
        try:
            scripts = self.profile.scripts()
            for old_script in scripts.find(USER_COSMETIC_SCRIPT):
                scripts.remove(old_script)
            data = {"user": self.adblock.cosmetic_payload().get("user", {})}
            source = r'''(function(){
              const DATA = __NEUTRON_DATA__;
              const invalid = s => !s || s.length > 800 || /\+js\(|#\?#|#%#|:has-text\(|:contains\(|:matches-css\(|:xpath\(|:-abp-/i.test(s);
              const host = (location.hostname || '').toLowerCase();
              const selectors = Object.entries(DATA.user || {})
                .filter(([d]) => d === '*' || host === d || host.endsWith('.' + d))
                .flatMap(([, values]) => values || []).filter(s => !invalid(s));
              function apply(){
                let el = document.getElementById('__neutron_user_cosmetics');
                if (!selectors.length) { if (el) el.remove(); return; }
                const root = document.head || document.documentElement;
                if (!root) return;
                if (!el) { el = document.createElement('style'); el.id = '__neutron_user_cosmetics'; root.appendChild(el); }
                const sheet = el.sheet;
                if (!sheet) return;
                while (sheet.cssRules.length) { try { sheet.deleteRule(0); } catch (_) { break; } }
                selectors.forEach(selector => {
                  try { sheet.insertRule(selector + '{display:none!important;visibility:hidden!important}', sheet.cssRules.length); }
                  catch (_) { /* skip only this selector */ }
                });
              }
              if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', apply, {once:true}); else apply();
            })();'''.replace("__NEUTRON_DATA__", json.dumps(data, ensure_ascii=False))
            script = QWebEngineScript()
            script.setName(USER_COSMETIC_SCRIPT)
            script.setSourceCode(source)
            script.setInjectionPoint(QWebEngineScript.InjectionPoint.DocumentCreation)
            script.setWorldId(QWebEngineScript.ScriptWorldId.MainWorld)
            script.setRunsOnSubFrames(True)
            scripts.insert(script)
        except Exception:
            log.exception("refresh cosmetic script")

    def _inject_scripts(self):
        scripts = self.profile.scripts()
        if self.vault and self.vault.available():
            s = QWebEngineScript()
            s.setName("neutron-pwd-capture")
            s.setSourceCode(CAPTURE_JS)
            s.setInjectionPoint(QWebEngineScript.InjectionPoint.DocumentCreation)
            s.setWorldId(QWebEngineScript.ScriptWorldId.MainWorld)
            s.setRunsOnSubFrames(False)
            scripts.insert(s)
        if self.path:  # Userscripts: วาง .js ไว้ที่ Profiles/<ชื่อ>/UserScripts/ (ทางเลือกสำรองแทน Extension)
            us = self.path / "UserScripts"
            us.mkdir(exist_ok=True)
            for f in sorted(us.glob("*.js")):
                try:
                    s = QWebEngineScript()
                    s.setName(f.name)
                    s.setSourceCode(f.read_text(encoding="utf-8"))
                    s.setInjectionPoint(QWebEngineScript.InjectionPoint.DocumentReady)
                    s.setWorldId(QWebEngineScript.ScriptWorldId.MainWorld)
                    scripts.insert(s)
                except OSError:
                    log.exception("userscript %s", f)
        self.refresh_cosmetic_script()

    def save_session(self, tabs):
        if self.path:
            write_json(self.path / "session.json", {"version": 2, "tabs": tabs})

    def load_session(self):
        d = read_json(self.path / "session.json", []) if self.path else []
        if isinstance(d, dict) and isinstance(d.get("tabs"), list):
            return d["tabs"]
        # Legacy session.json was a list of URL strings.
        return [{"url": u, "group": ""} for u in d] if isinstance(d, list) else []

    def save_permission(self, origin, kind, allowed):
        if not origin or not kind:
            return
        self.permission_rules.setdefault(origin, {})[kind] = bool(allowed)
        if self.permission_path:
            write_json(self.permission_path, self.permission_rules)

    def permission_decision(self, origin, kind):
        return self.permission_rules.get(origin, {}).get(kind)


def build_newtab(pd: ProfileData) -> str:
    cfg = pd.app.cfg
    pal = PALETTES["incognito" if pd.incognito else cfg["theme"] if cfg["theme"] in PALETTES else "dark"]
    tiles = ""
    for b in pd.bookmarks.items[:12]:
        if not b["url"].startswith(("http://", "https://")):
            continue
        t = html.escape(b["title"] or b["url"])
        tiles += f'<a class="tile" href="{html.escape(b["url"], quote=True)}"><span class="ic">{html.escape((b["title"] or "?")[:1].upper())}</span><span class="t">{t[:22]}</span></a>'
    tpl = SEARCH_ENGINES.get(cfg["search_engine"], SEARCH_ENGINES["Google"])
    sub = "Incognito - nothing is saved to disk" if pd.incognito else f"Profile: {html.escape(pd.name)}"
    page = Template(r"""<!doctype html><html lang="th"><head><meta charset="utf-8"><title>New Tab</title><style>
*{box-sizing:border-box}body{margin:0;min-height:100vh;display:flex;flex-direction:column;align-items:center;justify-content:center;
background:radial-gradient(circle at 50% 0%,$surface2,$bg 70%);color:$text;font-family:"Leelawadee UI","Noto Sans Thai","Segoe UI",sans-serif}
h1{font-size:68px;font-weight:200;letter-spacing:14px;margin:0;background:linear-gradient(90deg,$accent,$text);-webkit-background-clip:text;color:transparent}
.sub{color:$muted;margin:6px 0 30px}form{width:min(640px,86vw)}
input{width:100%;padding:16px 24px;font-size:17px;border-radius:30px;border:1px solid $border;background:$surface;color:$text;outline:none}
input:focus{border-color:$accent;box-shadow:0 0 0 3px $border}
.tiles{display:flex;flex-wrap:wrap;gap:14px;justify-content:center;margin-top:36px;max-width:760px}
.tile{width:104px;padding:14px 6px;border-radius:14px;text-decoration:none;color:$text;background:$surface;border:1px solid $border;text-align:center;transition:.15s}
.tile:hover{transform:translateY(-3px);border-color:$accent}
.ic{display:flex;width:44px;height:44px;margin:0 auto 8px;border-radius:50%;background:$accent;color:#fff;align-items:center;justify-content:center;font-size:20px;font-weight:600}
.t{font-size:12px;color:$muted;word-break:break-word}
</style></head><body><h1>NEUTRON</h1><div class="sub">$sub</div>
<form id="f"><input id="q" autofocus autocomplete="off" placeholder="ค้นหาหรือพิมพ์ URL / Search or type a URL"></form>
<div class="tiles">$tiles</div>
<script>var T=$tpl;document.getElementById('f').addEventListener('submit',function(e){e.preventDefault();
var v=document.getElementById('q').value.trim();if(!v)return;
if(v.indexOf(' ')<0&&(/^https?:\/\//i.test(v)||v.indexOf('.')>0)){location.href=/^https?:/i.test(v)?v:'https://'+v;}
else{location.href=T.replace('{}',encodeURIComponent(v));}});</script></body></html>""")
    return page.safe_substitute(**pal, sub=sub, tiles=tiles, tpl=json.dumps(tpl))


class NeutronSchemeHandler(QWebEngineUrlSchemeHandler):
    """neutron://newtab"""

    def __init__(self, pd: ProfileData):
        super().__init__(pd)
        self.pd = pd

    def requestStarted(self, job):
        try:
            if job.requestUrl().host() == "newtab":
                buf = QBuffer(job)
                buf.open(QIODevice.OpenModeFlag.WriteOnly)
                buf.write(build_newtab(self.pd).encode("utf-8"))
                buf.close()
                job.reply(b"text/html", buf)
            else:
                job.fail(QWebEngineUrlRequestJob.Error.UrlNotFound)
        except Exception:
            log.exception("scheme handler")
            job.fail(QWebEngineUrlRequestJob.Error.RequestFailed)


# ============================================================
# 6) Downloads + generic list dialog
# ============================================================
class DownloadManager(QObject):
    def __init__(self, cfg: Config):
        super().__init__()
        self.cfg, self.items = cfg, []
        self.meta = {}
        self._last_sample = time.monotonic()
        self.timer = QTimer(self)
        self.timer.setInterval(1000)
        self.timer.timeout.connect(self._sample_speeds)
        self.timer.start()

    @staticmethod
    def _category(name, mime=""):
        ext = Path(name or "").suffix.lower()
        if mime.startswith("image/") or ext in {".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp", ".svg", ".ico", ".tif", ".tiff", ".avif"}:
            return "Images"
        if mime.startswith("video/") or ext in {".mp4", ".mkv", ".avi", ".mov", ".webm", ".wmv", ".m4v"}:
            return "Videos"
        if mime.startswith("audio/") or ext in {".mp3", ".wav", ".flac", ".aac", ".ogg", ".m4a", ".opus"}:
            return "Audio"
        if ext in {".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx", ".txt", ".md", ".rtf", ".csv"}:
            return "Documents"
        if ext in {".zip", ".7z", ".rar", ".tar", ".gz", ".bz2", ".xz"}:
            return "Archives"
        if ext in {".exe", ".msi", ".msix", ".appx", ".apk", ".dmg", ".iso"}:
            return "Applications"
        return "Other"

    @staticmethod
    def _default_folder(cfg):
        return (cfg["download_dir"]
                or QStandardPaths.writableLocation(QStandardPaths.StandardLocation.DownloadLocation)
                or str(Path.home()))

    def handle(self, req: QWebEngineDownloadRequest):
        """Accept/cancel inside downloadRequested; accepted requests then download concurrently."""
        try:
            folder = self._default_folder(self.cfg)
            name = req.downloadFileName() or req.suggestedFileName() or "download"
            try:
                mime = req.mimeType() or ""
            except Exception:
                mime = ""
            self.items.append(req)
            self.meta[id(req)] = {
                "category": self._category(name, mime), "last_bytes": 0,
                "speed": 0.0, "last_time": time.monotonic(),
                "queued": False, "name": name,
            }

            # Qt owns the request and requires accept()/cancel() while handling
            # downloadRequested. Do not defer it to a non-modal dialog or queue.
            # The modal file dialog runs a nested Qt event loop; once it returns,
            # the request is accepted immediately and Chromium can transfer it
            # concurrently with every other accepted download.
            if self.cfg["ask_download"]:
                path, _ = QFileDialog.getSaveFileName(
                    QApplication.activeWindow(),
                    "Save file",
                    os.path.join(folder, name),
                    "All files (*)",
                )
                if not path:
                    req.cancel()
                    return
                folder, name = os.path.split(path)
                folder = folder or self._default_folder(self.cfg)

            self._accept_request(req, folder, name)
        except Exception:
            log.exception("download request handling")
            try:
                req.cancel()
            except Exception:
                pass

    def _accept_request(self, req, folder, name):
        try:
            Path(folder).mkdir(parents=True, exist_ok=True)
            req.setDownloadDirectory(str(folder))
            req.setDownloadFileName(str(name))
            req.accept()
            meta = self.meta.setdefault(id(req), {})
            meta.update({"queued": False, "name": str(name), "last_bytes": 0,
                         "speed": 0.0, "last_time": time.monotonic(),
                         "category": meta.get("category") or self._category(str(name), "")})
            try:
                req.receivedBytesChanged.connect(self._request_changed)
                req.stateChanged.connect(lambda *_: self._request_changed())
            except (AttributeError, RuntimeError):
                pass
            w = QApplication.activeWindow()
            if isinstance(w, QMainWindow):
                w.statusBar().showMessage(f"Downloading {name} ...", 4000)
        except Exception:
            log.exception("accept download")
            try:
                req.cancel()
            except Exception:
                pass

    def _request_changed(self, *_):
        # Speed is sampled centrally by the timer; this slot keeps UI refresh cheap.
        pass

    def cancel(self, index):
        try:
            self.items[index].cancel()
        except (IndexError, RuntimeError):
            pass

    def shutdown(self):
        self.timer.stop()
        states = QWebEngineDownloadRequest.DownloadState
        for req in list(self.items):
            try:
                if req.state() in (states.DownloadRequested, states.DownloadInProgress):
                    req.cancel()
            except RuntimeError:
                continue

    def _sample_speeds(self):
        now = time.monotonic()
        for req in list(self.items):
            meta = self.meta.get(id(req))
            if not meta or meta.get("queued"):
                continue
            try:
                received = max(0, int(req.receivedBytes()))
                elapsed = max(0.001, now - meta["last_time"])
                meta["speed"] = max(0.0, (received - meta["last_bytes"]) / elapsed)
                meta["last_bytes"], meta["last_time"] = received, now
            except RuntimeError:
                meta["speed"] = 0.0

    @staticmethod
    def _mb(n):
        return f"{n / 1048576:.1f} MB"

    @staticmethod
    def _speed(n):
        if n >= 1048576: return f"{n / 1048576:.2f} MB/s"
        if n >= 1024: return f"{n / 1024:.0f} KB/s"
        return f"{n:.0f} B/s" if n > 0 else "—"

    def rows(self, _q=""):
        S = QWebEngineDownloadRequest.DownloadState
        out = []
        q = (_q or "").lower()
        for i, req in enumerate(self.items):
            try:
                meta = self.meta.get(id(req), {})
                name = meta.get("name") or req.downloadFileName() or "download"
                category = meta.get("category", self._category(name)) if self.cfg.data.get("dl_categorize", True) else "—"
                if meta.get("queued"):
                    received, total, label = 0, -1, "Waiting for save location"
                else:
                    state, received, total = req.state(), req.receivedBytes(), req.totalBytes()
                    label = {S.DownloadCompleted: "Completed",
                             S.DownloadInProgress: ("Paused" if getattr(req, "isPaused", lambda: False)() else "Downloading"),
                             S.DownloadCancelled: "Cancelled", S.DownloadInterrupted: "Interrupted"}.get(state, "Pending")
                progress = f"{received * 100 // total}% ({self._mb(received)} / {self._mb(total)})" if total > 0 else self._mb(received)
                row = [name, category, progress, self._speed(meta.get("speed", 0.0)), label]
                if not q or q in " ".join(row).lower():
                    out.append((i, row))
            except RuntimeError:
                continue
        # Keep same-category files adjacent, which makes the category column useful as groups.
        out.sort(key=lambda item: (item[1][1], item[0]))
        return out

    def path_of(self, i):
        req = self.items[i]
        meta = self.meta.get(id(req), {})
        if meta.get("queued"):
            raise RuntimeError("This download is waiting for a save location.")
        folder = req.downloadDirectory()
        name = req.downloadFileName() or meta.get("name") or "download"
        if not folder:
            raise RuntimeError("The download has no destination folder yet.")
        return os.path.join(folder, name)


class ListDialog(QDialog):
    """Dialog ตารางอเนกประสงค์ (Bookmarks / History / Downloads / Passwords / Extensions)"""

    def __init__(self, parent, title, headers, loader, on_open=None, on_delete=None, on_clear=None,
                 searchable=False, extras=(), interval=0, widths=(300,)):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.resize(860, 520)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.loader, self.rows_, self.on_open, self.on_delete, self.on_clear = loader, [], on_open, on_delete, on_clear
        lay = QVBoxLayout(self)
        self.search = None
        if searchable:
            self.search = QLineEdit()
            self.search.setPlaceholderText("Search...")
            self.search.textChanged.connect(lambda *_: self.refresh())
            lay.addWidget(self.search)
        self.table = QTableWidget(0, len(headers))
        self.table.setHorizontalHeaderLabels(headers)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.table.verticalHeader().setVisible(False)
        self.table.horizontalHeader().setStretchLastSection(True)
        for i, w in enumerate(widths):
            self.table.setColumnWidth(i, w)
        self.table.doubleClicked.connect(lambda *_: self._open())
        lay.addWidget(self.table)
        row = QHBoxLayout()
        if on_open:
            b = QPushButton("Open")
            b.clicked.connect(lambda *_: self._open())
            row.addWidget(b)
        for label, fn in extras:
            b = QPushButton(label)
            b.clicked.connect(partial(self._extra, fn))
            row.addWidget(b)
        if on_delete:
            b = QPushButton("Delete")
            b.clicked.connect(lambda *_: self._delete())
            row.addWidget(b)
        if on_clear:
            b = QPushButton("Clear all")
            b.clicked.connect(lambda *_: self._clear())
            row.addWidget(b)
        row.addStretch()
        b = QPushButton("Close")
        b.clicked.connect(self.close)
        row.addWidget(b)
        lay.addLayout(row)
        self.refresh()
        if interval:
            t = QTimer(self)
            t.timeout.connect(self.refresh)
            t.start(interval)

    def selected_keys(self):
        rows = sorted({i.row() for i in self.table.selectedIndexes()})
        return [self.rows_[r][0] for r in rows if r < len(self.rows_)]

    def refresh(self):
        keep = set(self.selected_keys())
        self.rows_ = self.loader(self.search.text() if self.search else "")
        self.table.setRowCount(len(self.rows_))
        for r, (key, cols) in enumerate(self.rows_):
            for c, v in enumerate(cols):
                it = QTableWidgetItem(str(v))
                it.setToolTip(str(v))
                self.table.setItem(r, c, it)
            if key in keep:
                self.table.setRangeSelected(QTableWidgetSelectionRange(r, 0, r, self.table.columnCount() - 1), True)

    def _open(self):
        k = self.selected_keys()
        if k and self.on_open:
            self.on_open(k)

    def _delete(self):
        k = self.selected_keys()
        if k and self.on_delete:
            self.on_delete(k)
            self.refresh()

    def _clear(self):
        if QMessageBox.question(self, APP_NAME, "Clear everything in this list?") == QMessageBox.StandardButton.Yes:
            self.on_clear()
            self.refresh()

    def _extra(self, fn, *_):
        try:
            fn(self.selected_keys())
        except Exception as e:
            log.exception("dialog extra")
            QMessageBox.warning(self, APP_NAME, str(e))
        self.refresh()


# ============================================================
# 7) Web page / view / tab
# ============================================================
class WebPage(QWebEnginePage):
    def __init__(self, profile, owner, parent=None):
        super().__init__(profile, parent)
        self.owner = owner
        self._compatibility_host = ""
        self._compatibility_originals = {}

    def _apply_site_compatibility(self, url: QUrl):
        """Apply per-page rendering workarounds before a known fragile site loads."""
        host = (url.host() or "").lower().rstrip(".")
        is_dekd = host == "novel.dek-d.com" or host.endswith(".novel.dek-d.com")
        settings = self.settings()
        attrs = QWebEngineSettings.WebAttribute
        names = ("WebGLEnabled", "Accelerated2dCanvasEnabled")

        if is_dekd:
            if self._compatibility_host == host:
                return
            # Preserve the effective page values, then disable only the two
            # acceleration features. Other sites retain the profile's settings.
            for name in names:
                attribute = getattr(attrs, name, None)
                if attribute is None:
                    continue
                if attribute not in self._compatibility_originals:
                    self._compatibility_originals[attribute] = settings.testAttribute(attribute)
                settings.setAttribute(attribute, False)
            self._compatibility_host = host
            log.info("Applied Dek-D renderer compatibility mode: %s", host)
        elif self._compatibility_host:
            for attribute, original in tuple(self._compatibility_originals.items()):
                try:
                    settings.setAttribute(attribute, original)
                except Exception:
                    log.exception("Could not restore page rendering setting %s", attribute)
            self._compatibility_originals.clear()
            self._compatibility_host = ""
            log.info("Restored normal page rendering settings after leaving Dek-D")

    def acceptNavigationRequest(self, url, navigation_type, is_main_frame):
        if is_main_frame:
            try:
                self._apply_site_compatibility(url)
            except Exception:
                log.exception("site compatibility setup failed: %s", url.toString())
        return super().acceptNavigationRequest(url, navigation_type, is_main_frame)

    def createWindow(self, wtype):
        try:
            return self.owner.create_page_for(wtype, self.profile())
        except Exception:
            log.exception("createWindow")
            return None

    def javaScriptConsoleMessage(self, level, message, line, source):
        try:
            if message.startswith(PWD_PREFIX):
                self.owner.on_credentials_captured(self, message[len(PWD_PREFIX):])
                return
            if message.startswith("__NEUTRON_BLOCK__"):
                self.owner.on_element_selected(message[len("__NEUTRON_BLOCK__"):])
                return
        except Exception:
            log.exception("page console bridge")
            return

        # Keep diagnostics for Neutron's own tools without flooding logs with
        # console output from every third-party website.
        try:
            if self.url().host().lower() == BG_HOST:
                level_name = getattr(level, "name", str(level))
                if "Error" in level_name or "Warning" in level_name:
                    log.warning("Background Remover JS %s at %s:%s: %s",
                                level_name, source, line, message)
        except Exception:
            log.debug("Could not record internal-page console message", exc_info=True)


class WebView(QWebEngineView):
    def __init__(self, owner, profile):
        super().__init__()
        self.owner, self.tab = owner, None
        self.force_right_click = False
        self.setPage(WebPage(profile, owner, self))

    def contextMenuEvent(self, ev):
        """Build a fresh, view-owned context menu for every request.

        QWebEngineView.createStandardContextMenu() is the supported Qt API;
        QWebEnginePage does not own this method. The media request is valid only
        during this event, so copy its URL before opening the menu.
        """
        if getattr(self, "_context_menu_open", False):
            ev.accept()
            return
        self._context_menu_open = True
        menu = None
        try:
            page = self.page()
            if page is None:
                ev.accept()
                return

            # Correct API: createStandardContextMenu belongs to QWebEngineView.
            menu = self.createStandardContextMenu()
            if menu is None:
                raise RuntimeError("Qt did not create a standard context menu")

            # Parent the menu to this view for deterministic QObject ownership.
            menu.setParent(self)
            try:
                for act in list(menu.actions()):
                    if "inspect" in act.text().lower() or act is page.action(QWebEnginePage.WebAction.InspectElement):
                        menu.removeAction(act)
            except RuntimeError:
                log.debug("Could not filter one standard context-menu action", exc_info=True)

            # Select/copy only the DOM element under the context-click point,
            # not the whole document. Insert immediately after Save Page where possible.
            click_pos = ev.pos()
            select_action = QAction("Select All (this element) + Copy", menu)
            select_action.triggered.connect(
                lambda x=click_pos.x(), y=click_pos.y(), v=self:
                    self.owner.select_element_text(v, x, y)
            )
            standard_actions = menu.actions()
            save_pos = next((i for i, a in enumerate(standard_actions)
                             if a is page.action(QWebEnginePage.WebAction.SavePage)
                             or "save page" in a.text().lower()), -1)
            before = standard_actions[save_pos + 1] if 0 <= save_pos + 1 < len(standard_actions) else None
            menu.insertAction(before, select_action)

            menu.addSeparator()
            menu.addAction("View page source", lambda view=self: self.owner.view_source(view))
            if self.tab is not None:
                menu.addAction("Inspect Element", self.tab.inspect)
            menu.addAction("Block element (Neutron AdBlock)", lambda view=self: self.owner.start_element_picker(view))

            # Qt 6.2+: QWebEngineView.lastContextMenuRequest() replaces the old
            # page contextMenuData() path in newer Qt releases.
            media_url = QUrl()
            try:
                request_getter = getattr(self, "lastContextMenuRequest", None)
                request = request_getter() if callable(request_getter) else None
                if request is not None:
                    media_getter = getattr(request, "mediaUrl", None)
                    candidate = media_getter() if callable(media_getter) else QUrl()
                    if isinstance(candidate, QUrl) and not candidate.isEmpty():
                        media_url = QUrl(candidate)
                else:
                    # Compatibility path for older Qt 6 builds.
                    legacy_getter = getattr(page, "contextMenuData", None)
                    legacy = legacy_getter() if callable(legacy_getter) else None
                    media_getter = getattr(legacy, "mediaUrl", None) if legacy is not None else None
                    candidate = media_getter() if callable(media_getter) else QUrl()
                    if isinstance(candidate, QUrl) and not candidate.isEmpty():
                        media_url = QUrl(candidate)
            except (RuntimeError, AttributeError, TypeError):
                log.debug("No image/media context data for this right-click", exc_info=True)

            if not media_url.isEmpty():
                copied_url = QUrl(media_url)
                menu.addAction("Open image in new tab", lambda u=copied_url: self.owner.add_tab(QUrl(u)))
                menu.addAction("Copy image address", lambda u=copied_url.toString(): QApplication.clipboard().setText(u))
                # Defer the modal file dialogs until the native context menu has
                # returned from exec(); nested menus can otherwise leave the
                # view in a stale context-menu state on some Qt builds.
                menu.addAction("Save image as...", lambda u=copied_url: QTimer.singleShot(
                    0, lambda: self.owner.save_context_image(QUrl(u))
                ))

            menu.addSeparator()
            menu.addAction(
                "Disable Right Click on this tab" if self.force_right_click else "Enable Right Click on this tab",
                self.owner.toggle_right_click,
            )

            menu.exec(ev.globalPos())
            ev.accept()
        except Exception:
            log.exception("context menu failed")
            # Fall back to Qt's native menu; do not leave a sticky state or
            # permanently disable subsequent right-click events.
            try:
                super().contextMenuEvent(ev)
            except Exception:
                log.exception("native context menu fallback failed")
                ev.accept()
        finally:
            self._context_menu_open = False
            if menu is not None:
                try:
                    menu.close()
                    menu.deleteLater()
                except RuntimeError:
                    pass



class BrowserTab(QSplitter):
    def __init__(self, owner, profile):
        super().__init__(Qt.Orientation.Vertical)
        self.loading, self.progress, self.dev_view = False, 0, None
        self.group = ""
        self.pinned = False
        self.muted = False
        self.suspended = False
        self.setChildrenCollapsible(False)
        self.setHandleWidth(3)
        self.view = WebView(owner, profile)
        self.view.tab = self
        self.addWidget(self.view)

    def show_devtools(self):
        if self.dev_view is None:
            self.dev_view = QWebEngineView()
            dev_page = QWebEnginePage(self.view.page().profile(), self.dev_view)
            self.dev_view.setPage(dev_page)
            self.view.page().setDevToolsPage(dev_page)
            self.addWidget(self.dev_view)
            self.setSizes([520, 380])
        self.dev_view.show()

    def toggle_devtools(self):
        if self.dev_view is not None and self.dev_view.isVisible():
            self.dev_view.hide()
        else:
            self.show_devtools()

    def inspect(self):
        self.show_devtools()
        self.view.page().triggerAction(QWebEnginePage.WebAction.InspectElement)

    def dispose(self):
        try:
            if self.dev_view is not None:
                self.dev_view.deleteLater()
            self.view.setUrl(QUrl("about:blank"))
            self.view.deleteLater()
        except RuntimeError:
            pass


class TabBar(QTabBar):
    newTabRequested = pyqtSignal()
    closeRequested = pyqtSignal(int)

    def mouseDoubleClickEvent(self, e):
        if self.tabAt(e.position().toPoint()) < 0:
            self.newTabRequested.emit()
        else:
            super().mouseDoubleClickEvent(e)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.MiddleButton:
            i = self.tabAt(e.position().toPoint())
            if i >= 0:
                self.closeRequested.emit(i)
                return
        super().mouseReleaseEvent(e)


class PopupWindow(QMainWindow):
    """window.open() แบบ popup (WebDialog)"""

    def __init__(self, owner, profile, url: Optional[QUrl] = None):
        super().__init__(owner)
        self.setWindowIcon(QApplication.instance().windowIcon())
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.resize(480, 640)
        self.view = WebView(owner, profile)
        w = QWidget()
        lay = QVBoxLayout(w)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        self.addr = QLineEdit()
        self.addr.setReadOnly(True)
        lay.addWidget(self.addr)
        lay.addWidget(self.view)
        self.setCentralWidget(w)
        pg = self.view.page()
        pg.titleChanged.connect(lambda t: self.setWindowTitle(t or APP_NAME))
        pg.urlChanged.connect(lambda u: self.addr.setText(u.toString()))
        pg.geometryChangeRequested.connect(lambda r: self.setGeometry(r))
        pg.windowCloseRequested.connect(self.close)
        if url is not None:
            self.view.load(url)

    def closeEvent(self, e):
        try:
            self.view.setUrl(QUrl("about:blank"))
        except RuntimeError:
            pass
        super().closeEvent(e)


# ============================================================
# 8) Settings dialog
# ============================================================
class SettingsDialog(QDialog):
    def __init__(self, win: "BrowserWindow"):
        super().__init__(win)
        self.win, self.cfg = win, win.cfg
        self.setWindowTitle("Neutron Settings")
        self.resize(640, 580)
        lay = QVBoxLayout(self)
        tabs = QTabWidget()
        lay.addWidget(tabs)
        c = self.cfg

        g = QWidget()
        f = QFormLayout(g)
        self.c_startup = QComboBox()
        for k, label in STARTUP_MODES:
            self.c_startup.addItem(label, k)
        self.c_startup.setCurrentIndex(max(0, self.c_startup.findData(c["startup_mode"])))
        self.e_home = QLineEdit(c["homepage"])
        self.t_urls = QPlainTextEdit(c["startup_urls"])
        self.t_urls.setFixedHeight(80)
        self.t_urls.setPlaceholderText("One URL per line (for 'Open specific pages')")
        self.c_search = QComboBox()
        self.c_search.addItems(list(SEARCH_ENGINES))
        self.c_search.setCurrentText(c["search_engine"])
        self.c_theme = QComboBox()
        self.c_theme.addItems(["dark", "light"])
        self.c_theme.setCurrentText(c["theme"])
        self.e_dl = QLineEdit(c["download_dir"])
        self.e_dl.setPlaceholderText("Default: system Downloads folder")
        bd = QPushButton("Browse...")
        bd.clicked.connect(self._browse)
        rd = QHBoxLayout()
        rd.addWidget(self.e_dl)
        rd.addWidget(bd)
        self.k_ask = QCheckBox("Ask where to save each file")
        self.k_ask.setChecked(c["ask_download"])
        self.k_dlcat = QCheckBox("Categorize downloads (Images / Videos / Documents / etc.)")
        self.k_dlcat.setChecked(c.data.get("dl_categorize", True))
        self.k_bm = QCheckBox("Show bookmarks bar")
        self.k_bm.setChecked(c["show_bookmarks_bar"])
        for label, w in (("On startup", self.c_startup), ("Homepage", self.e_home), ("Startup pages", self.t_urls),
                         ("Search engine", self.c_search), ("Theme", self.c_theme), ("Download folder", rd)):
            f.addRow(label, w)
        f.addRow("", self.k_ask)
        f.addRow("", self.k_dlcat)
        f.addRow("", self.k_bm)
        tabs.addTab(g, "General")

        t = QWidget()
        f2 = QFormLayout(t)
        self.f_std, self.f_sans = self._fc(c["font_standard"]), self._fc(c["font_sans"])
        self.f_serif, self.f_fixed = self._fc(c["font_serif"]), self._fc(c["font_fixed"])
        self.s_size = self._spin(c["font_size"], 8, 40)
        self.s_fixed = self._spin(c["font_fixed_size"], 8, 40)
        self.s_min = self._spin(c["font_min_size"], 0, 30)
        self.s_zoom = self._spin(c["default_zoom"], 30, 300)
        self.s_zoom.setSuffix(" %")
        self.e_lang = QLineEdit(c["accept_language"])
        for label, w in (("Standard font", self.f_std), ("Sans-serif font", self.f_sans), ("Serif font", self.f_serif),
                         ("Fixed-width font", self.f_fixed), ("Default font size", self.s_size),
                         ("Fixed font size", self.s_fixed), ("Minimum font size", self.s_min),
                         ("Default page zoom", self.s_zoom), ("Accept-Language", self.e_lang)):
            f2.addRow(label, w)
        pb = QPushButton("Thai reading preset (auto fonts, size 16, min 12)")
        pb.clicked.connect(self._thai_preset)
        f2.addRow("", pb)
        f2.addRow("", QLabel("Reload open pages to see font changes."))
        tabs.addTab(t, "Fonts & Display")

        p = QWidget()
        f3 = QFormLayout(p)
        self.k_pw = QCheckBox("Offer to save passwords (encrypted with a master password)")
        self.k_pw.setChecked(c["save_passwords"])
        self.k_js = QCheckBox("Enable JavaScript")
        self.k_js.setChecked(c["javascript"])
        self.k_pop = QCheckBox("Allow pop-ups / window.open()")
        self.k_pop.setChecked(c["popups"])
        self.k_wipe = QCheckBox("Wipe cookies, cache & site data (localStorage/IndexedDB) when Neutron closes")
        self.k_wipe.setChecked(c["clear_on_exit"])
        self.k_dark = QCheckBox("Force dark mode on web pages")
        self.k_dark.setChecked(c["force_dark_web"])
        self.k_adblock = QCheckBox("Enable AdGuard-compatible ad and tracker blocking")
        self.k_adblock.setChecked(c["adblock_enabled"])
        self.s_reader = self._spin(c["reader_font_size"], 12, 30)
        self.c_reader_theme = QComboBox()
        self.c_reader_theme.addItems(["light", "sepia", "dark"])
        self.c_reader_theme.setCurrentText(c["reader_theme"])
        for w in (self.k_pw, self.k_js, self.k_pop, self.k_wipe, self.k_dark, self.k_adblock):
            f3.addRow(w)
        b1 = QPushButton("Clear browsing data now (history, cache, cookies)")
        b1.clicked.connect(win.clear_browsing_data)
        b2 = QPushButton("Manage saved passwords...")
        b2.clicked.connect(win.show_passwords)
        f3.addRow(b1)
        f3.addRow(b2)
        f3.addRow("Reader font size", self.s_reader)
        f3.addRow("Reader theme", self.c_reader_theme)
        tabs.addTab(p, "Privacy & Tools")

        row = QHBoxLayout()
        row.addStretch()
        ok, cancel = QPushButton("Save"), QPushButton("Cancel")
        ok.setObjectName("go")
        ok.clicked.connect(self._save)
        cancel.clicked.connect(self.reject)
        row.addWidget(cancel)
        row.addWidget(ok)
        lay.addLayout(row)

    @staticmethod
    def _spin(v, lo, hi):
        s = QSpinBox()
        s.setRange(lo, hi)
        s.setValue(int(v))
        return s

    @staticmethod
    def _fc(value):
        c = QComboBox()
        c.setEditable(True)
        c.addItem("")
        c.addItems(QFontDatabase.families())
        c.setCurrentText(value)
        c.lineEdit().setPlaceholderText("Auto (Thai-friendly)")
        return c

    def _browse(self):
        d = QFileDialog.getExistingDirectory(self, "Download folder", self.e_dl.text())
        if d:
            self.e_dl.setText(d)

    def _thai_preset(self):
        for c in (self.f_std, self.f_sans, self.f_serif, self.f_fixed):
            c.setCurrentText("")
        self.s_size.setValue(16)
        self.s_fixed.setValue(13)
        self.s_min.setValue(12)
        self.e_lang.setText(DEFAULTS["accept_language"])

    def _save(self):
        c = self.cfg
        if self.k_adblock.isChecked() and not bool(c["adblock_enabled"]):
            answer = QMessageBox.warning(
                self, "Enable AdBlock?",
                "AdBlock may slow down or break parts of some websites, including search pages. "
                "If a website behaves incorrectly, add it to Allowlist or turn AdBlock off temporarily.\n\nEnable AdBlock?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No,
            )
            if answer != QMessageBox.StandardButton.Yes:
                self.k_adblock.setChecked(False)
        c["startup_mode"] = self.c_startup.currentData()
        c["homepage"] = self.e_home.text().strip() or DEFAULTS["homepage"]
        c["startup_urls"] = self.t_urls.toPlainText()
        c["search_engine"], c["theme"] = self.c_search.currentText(), self.c_theme.currentText()
        c["download_dir"], c["ask_download"] = self.e_dl.text().strip(), self.k_ask.isChecked()
        c["dl_categorize"] = self.k_dlcat.isChecked()
        c["show_bookmarks_bar"] = self.k_bm.isChecked()
        c["font_standard"], c["font_sans"] = self.f_std.currentText().strip(), self.f_sans.currentText().strip()
        c["font_serif"], c["font_fixed"] = self.f_serif.currentText().strip(), self.f_fixed.currentText().strip()
        c["font_size"], c["font_fixed_size"], c["font_min_size"] = self.s_size.value(), self.s_fixed.value(), self.s_min.value()
        c["default_zoom"], c["accept_language"] = self.s_zoom.value(), self.e_lang.text().strip() or DEFAULTS["accept_language"]
        c["save_passwords"], c["javascript"], c["popups"] = self.k_pw.isChecked(), self.k_js.isChecked(), self.k_pop.isChecked()
        c["clear_on_exit"], c["force_dark_web"] = self.k_wipe.isChecked(), self.k_dark.isChecked()
        c["adblock_enabled"] = self.k_adblock.isChecked()
        c["reader_font_size"] = self.s_reader.value()
        c["reader_theme"] = self.c_reader_theme.currentText()
        c.save()
        self.win.ctx.apply_settings()
        self.win._set_adblock_enabled(c["adblock_enabled"])
        self.accept()


# ============================================================
# 9) Main browser window
# ============================================================
class BrowserWindow(QMainWindow):
    def __init__(self, ctx: "NeutronApp", pd: ProfileData):
        super().__init__()
        self.ctx, self.pd, self.cfg = ctx, pd, ctx.cfg
        self.setWindowIcon(QApplication.instance().windowIcon())
        self.closed_tabs: list[str] = []
        self._last_cred = ("", 0.0)
        self._comp_ts = 0.0
        self._snap_timer = QTimer(self)
        self._snap_timer.setSingleShot(True)
        self._snap_timer.timeout.connect(self._save_session_snapshot_now)
        pd.windows += 1
        self.resize(1280, 820)
        self._build_ui()
        self._build_actions()
        self._build_menu()
        self.apply_theme()
        self._suspend_timer = QTimer(self)
        self._suspend_timer.timeout.connect(self._auto_suspend_check)
        self._suspend_timer.start(60000)
        self._vault_timer = QTimer(self)
        self._vault_timer.timeout.connect(self._vault_auto_lock_check)
        self._vault_timer.start(30000)
        if not pd.incognito and self.cfg["window_geometry"] and not ctx.windows:
            try:
                self.restoreGeometry(QByteArray.fromBase64(self.cfg["window_geometry"].encode()))
            except Exception:
                pass
        pd.bookmarks.changed.connect(self.refresh_bookmarks_bar)
        self.refresh_bookmarks_bar()

    # ---------- UI ----------
    def _nbtn(self, text, tip, slot):
        b = QToolButton()
        b.setObjectName("nav")
        b.setText(text)
        b.setToolTip(tip)
        b.clicked.connect(lambda *_: slot())
        return b

    def _build_ui(self):
        central = QWidget()
        root = QVBoxLayout(central)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)
        self.chrome = QWidget()
        self.chrome.setObjectName("chrome")
        cl = QVBoxLayout(self.chrome)
        cl.setContentsMargins(0, 0, 0, 0)
        cl.setSpacing(0)

        trow = QHBoxLayout()
        trow.setContentsMargins(8, 0, 8, 0)
        self.tabbar = TabBar()
        self.tabbar.setMovable(True)
        self.tabbar.setExpanding(False)
        self.tabbar.setDrawBase(False)
        self.tabbar.setTabsClosable(False)
        self.tabbar.setElideMode(Qt.TextElideMode.ElideRight)
        self.tabbar.currentChanged.connect(self.on_tab_changed)
        self.tabbar.tabMoved.connect(self.on_tab_moved)
        self.tabbar.newTabRequested.connect(lambda: self.add_tab(NEWTAB_URL))
        self.tabbar.closeRequested.connect(self.close_tab)
        self.tabbar.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.tabbar.customContextMenuRequested.connect(self.tab_context_menu)
        trow.addWidget(self.tabbar, 0)
        plus = self._nbtn("+", "New tab (Ctrl+T)", lambda: self.add_tab(NEWTAB_URL))
        trow.addWidget(plus)
        trow.addStretch()
        self.badge = QLabel("Incognito" if self.pd.incognito else self.pd.name)
        self.badge.setObjectName("badge")
        self.badge.setToolTip("Current profile")
        trow.addWidget(self.badge)
        cl.addLayout(trow)

        nav = QWidget()
        nav.setObjectName("navbar")
        h = QHBoxLayout(nav)
        h.setContentsMargins(8, 6, 8, 6)
        h.setSpacing(4)
        self.btn_back = self._nbtn("←", "Back (Alt+Left)", self.go_back)
        self.btn_fwd = self._nbtn("→", "Forward (Alt+Right)", self.go_forward)
        self.btn_reload = self._nbtn("↻", "Reload (F5)", self.reload_or_stop)
        self.btn_home = self._nbtn("⌂", "Home (Alt+Home)", self.go_home)
        for b in (self.btn_back, self.btn_fwd, self.btn_reload, self.btn_home):
            h.addWidget(b)
        self.urlframe = QFrame()
        self.urlframe.setObjectName("urlframe")
        uh = QHBoxLayout(self.urlframe)
        uh.setContentsMargins(12, 0, 6, 0)
        self.lock = QLabel("ⓘ")
        self.urlbar = QLineEdit()
        self.urlbar.setObjectName("urlbar")
        self.urlbar.setPlaceholderText("ค้นหาหรือพิมพ์ URL / Search or type a URL")
        self.urlbar.returnPressed.connect(lambda: self.navigate(self.urlbar.text()))
        self.urlbar.installEventFilter(self)
        self.comp_model = QStringListModel(self)
        comp = QCompleter(self.comp_model, self)
        comp.setCaseSensitivity(Qt.CaseSensitivity.CaseInsensitive)
        comp.setFilterMode(Qt.MatchFlag.MatchContains)
        comp.setCompletionMode(QCompleter.CompletionMode.PopupCompletion)
        comp.activated[str].connect(self.navigate)
        self.urlbar.setCompleter(comp)
        self.btn_star = QToolButton()
        self.btn_star.setObjectName("star")
        self.btn_star.setText("☆")
        self.btn_star.setToolTip("Bookmark this page (Ctrl+D)")
        self.btn_star.clicked.connect(lambda *_: self.toggle_bookmark())
        uh.addWidget(self.lock)
        uh.addWidget(self.urlbar, 1)
        uh.addWidget(self.btn_star)
        # Allow the URL bar to expand and fill all remaining horizontal toolbar space.
        from PyQt6.QtWidgets import QSizePolicy
        self.urlframe.setMinimumWidth(150)
        self.urlframe.setMaximumWidth(16777215)
        self.urlframe.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.urlbar.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        h.addWidget(self.urlframe, 1)
        go = QPushButton("Go")
        go.setObjectName("go")
        go.setCursor(Qt.CursorShape.PointingHandCursor)
        go.setFixedWidth(96)  # ประมาณ 2.5 cm; ไม่ยืดตามพื้นที่ว่างของ Toolbar
        go.setMinimumHeight(32)
        go.setToolTip("Go to the entered address")
        go.clicked.connect(lambda *_: self.navigate(self.urlbar.text()))
        h.addWidget(go, 0, Qt.AlignmentFlag.AlignLeft)

        self.btn_downloads = self._nbtn("↓", "Download history", self.toggle_download_tray)
        self.btn_downloads.setToolTip("Downloads / Download history")
        h.addWidget(self.btn_downloads)
        self.btn_shields = self._nbtn("🛡", "AdBlock settings / site protection", self.show_adblock)
        self.btn_rightclick = self._nbtn("🖱", "Force right-click on this tab", self.toggle_right_click)
        self.btn_images = self._nbtn("▧", "Save all pictures on this page", self.save_all_pictures)
        self.btn_screenshot = self._nbtn("▣", "Capture screenshot", self.capture_screenshot)
        self.btn_reader = self._nbtn("A", "Reader mode", self.reader_mode)
        self.btn_ocr = self._nbtn("OCR", "Extract text from images and PDF", self.open_ocr)
        self.btn_ocr.setStyleSheet("font-size:12px;font-weight:700;")
        self.btn_bgremove = self._nbtn("BG", "Remove image background with AI", self.open_background_remover)
        self.btn_bgremove.setStyleSheet("font-size:11px;font-weight:700;")
        self.btn_calculator = self._nbtn("CALC", "Standard calculator", self.open_calculator)
        self.btn_b64_decode = self._nbtn("D64", "Base64 decoder / file restorer", self.open_base64_decoder)
        self.btn_b64_encode = self._nbtn("E64", "Base64 encoder", self.open_base64_encoder)
        for b in (self.btn_calculator, self.btn_b64_decode, self.btn_b64_encode):
            b.setStyleSheet("font-size:11px;font-weight:700;")
        self.btn_music = self._nbtn("🎵", "Web Music Player (music_player.html)", self.open_music_player)
        self.btn_game = self._nbtn("🎮", "Neutron Game Hub (game_hub.html)", self.open_game_hub)
        self.btn_permissions = self._nbtn("⚙", "Website permissions", self.show_permissions)
        for b in (self.btn_shields, self.btn_rightclick, self.btn_images, self.btn_screenshot,
                  self.btn_reader, self.btn_ocr, self.btn_bgremove, self.btn_calculator,
                  self.btn_b64_decode, self.btn_b64_encode, self.btn_music, self.btn_game,
                  self.btn_permissions):
            h.addWidget(b)

        self.btn_menu = QToolButton()
        self.btn_menu.setObjectName("menuBtn")
        self.btn_menu.setText("☰")
        self.btn_menu.setPopupMode(QToolButton.ToolButtonPopupMode.InstantPopup)
        self.btn_menu.setStyleSheet("font-size:18px;")
        h.addWidget(self.btn_menu)
        cl.addWidget(nav)

        self.bmbar = QWidget()
        self.bmbar.setObjectName("bmbar")
        self.bm_layout = QHBoxLayout(self.bmbar)
        self.bm_layout.setContentsMargins(8, 2, 8, 2)
        self.bm_layout.setSpacing(2)
        cl.addWidget(self.bmbar)
        self.bmbar.setVisible(bool(self.cfg["show_bookmarks_bar"]))

        self.progress = QProgressBar()
        self.progress.setObjectName("progress")
        self.progress.setTextVisible(False)
        self.progress.setRange(0, 100)
        self.progress.hide()
        cl.addWidget(self.progress)
        root.addWidget(self.chrome)

        self.stack = QStackedWidget()
        root.addWidget(self.stack, 1)

        self.findbar = QWidget()
        self.findbar.setObjectName("findbar")
        fh = QHBoxLayout(self.findbar)
        fh.setContentsMargins(8, 4, 8, 4)
        self.find_edit = QLineEdit()
        self.find_edit.setPlaceholderText("Find in page")
        self.find_edit.textChanged.connect(lambda t: self.find(t, False))
        self.find_edit.returnPressed.connect(lambda: self.find(self.find_edit.text(), False))
        pb, nb, cb = self._nbtn("▲", "Previous", lambda: self.find(self.find_edit.text(), True)), \
            self._nbtn("▼", "Next", lambda: self.find(self.find_edit.text(), False)), self._nbtn("✕", "Close", self.close_find)
        for w in (self.find_edit, pb, nb, cb):
            fh.addWidget(w)
        esc = QAction(self.findbar)
        esc.setShortcut(QKeySequence("Esc"))
        esc.setShortcutContext(Qt.ShortcutContext.WidgetWithChildrenShortcut)
        esc.triggered.connect(self.close_find)
        self.findbar.addAction(esc)
        self.findbar.hide()
        root.addWidget(self.findbar)
        self.setCentralWidget(central)
        self._build_download_tray()

        self.load_label = QLabel("")
        self.statusBar().addPermanentWidget(self.load_label)
        self.statusBar().showMessage("Ready", 2000)

    def _build_download_tray(self):
        """Create a lightweight dropdown tray for all download file types."""
        self.download_tray = QFrame(
            self, Qt.WindowType.Popup | Qt.WindowType.FramelessWindowHint
        )
        self.download_tray.setObjectName("downloadTray")
        self.download_tray.setMinimumWidth(440)
        self.download_tray.setMaximumWidth(560)
        self.download_tray.setStyleSheet(
            "QFrame#downloadTray{background:#202938;border:1px solid #526079;border-radius:10px;}"
            "QListWidget{background:transparent;border:0;}"
            "QListWidget::item{border-bottom:1px solid #3a465b;padding:4px;}"
        )
        tray_layout = QVBoxLayout(self.download_tray)
        tray_layout.setContentsMargins(10, 10, 10, 10)
        header = QHBoxLayout()
        title = QLabel("Downloads")
        title.setStyleSheet("font-weight:700;font-size:15px;")
        header.addWidget(title)
        header.addStretch()
        all_downloads = QPushButton("Manage all")
        all_downloads.clicked.connect(lambda: (self.download_tray.hide(), self.show_downloads()))
        header.addWidget(all_downloads)
        tray_layout.addLayout(header)
        self.download_tray_list = QListWidget()
        self.download_tray_list.setMinimumHeight(120)
        self.download_tray_list.setMaximumHeight(390)
        tray_layout.addWidget(self.download_tray_list)
        self.download_tray_hint = QLabel("")
        self.download_tray_hint.setStyleSheet("color:#aab6c9;font-size:11px;")
        tray_layout.addWidget(self.download_tray_hint)
        self.download_tray.installEventFilter(self)
        self.download_tray_timer = QTimer(self)
        self.download_tray_timer.setInterval(900)
        self.download_tray_timer.timeout.connect(self._refresh_download_tray)

    def toggle_download_tray(self):
        if self.download_tray.isVisible():
            self.download_tray.hide()
            self.download_tray_timer.stop()
            return
        self._refresh_download_tray()
        self.download_tray.adjustSize()
        width = max(440, self.download_tray.sizeHint().width())
        self.download_tray.resize(width, min(500, max(170, self.download_tray.sizeHint().height())))
        anchor = self.btn_downloads.mapToGlobal(self.btn_downloads.rect().bottomLeft())
        x, y = anchor.x() - width + self.btn_downloads.width(), anchor.y() + 5
        screen = self.screen().availableGeometry() if self.screen() else self.geometry()
        x = max(screen.left() + 6, min(x, screen.right() - width - 6))
        if y + self.download_tray.height() > screen.bottom():
            y = max(screen.top() + 6, anchor.y() - self.download_tray.height() - 5)
        self.download_tray.move(x, y)
        self.download_tray.show()
        self.download_tray.raise_()
        self.download_tray_timer.start()

    def _download_open_path(self, index):
        try:
            path = Path(self.ctx.downloads.path_of(index))
            if path.is_file():
                QDesktopServices.openUrl(QUrl.fromLocalFile(str(path)))
            else:
                self.statusBar().showMessage("The downloaded file is not available yet.", 2500)
        except Exception as exc:
            log.exception("open downloaded file")
            self.statusBar().showMessage(f"Cannot open download: {exc}", 4000)

    def _download_show_folder(self, index):
        try:
            path = Path(self.ctx.downloads.path_of(index))
            folder = path.parent
            if folder.is_dir():
                QDesktopServices.openUrl(QUrl.fromLocalFile(str(folder)))
        except Exception as exc:
            log.exception("show downloaded file folder")
            self.statusBar().showMessage(f"Cannot open download folder: {exc}", 4000)

    def _refresh_download_tray(self):
        if not hasattr(self, "download_tray_list"):
            return
        dm = self.ctx.downloads
        rows = dm.rows()
        self.download_tray_list.clear()
        if not rows:
            item = QListWidgetItem("No downloads yet")
            item.setFlags(Qt.ItemFlag.NoItemFlags)
            self.download_tray_list.addItem(item)
            self.download_tray_hint.setText("Downloaded files of every type appear here.")
            return
        completed = 0
        for index, values in reversed(rows):
            name, category, progress, speed, state = values
            if state == "Completed":
                completed += 1
            item = QListWidgetItem(self.download_tray_list)
            row_widget = QWidget()
            row_layout = QHBoxLayout(row_widget)
            row_layout.setContentsMargins(4, 5, 4, 5)
            details = QVBoxLayout()
            name_label = QLabel(str(name))
            name_label.setToolTip(str(name))
            name_label.setStyleSheet("font-weight:600;")
            name_label.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
            meta_label = QLabel(f"{category} · {state} · {progress} · {speed}")
            meta_label.setStyleSheet("color:#aab6c9;font-size:10px;")
            details.addWidget(name_label)
            details.addWidget(meta_label)
            row_layout.addLayout(details, 1)
            open_btn = QPushButton("Open")
            folder_btn = QPushButton("Show folder")
            try:
                path = Path(dm.path_of(index))
                ready = path.is_file() and state == "Completed"
                folder_ready = path.parent.is_dir()
            except Exception:
                ready = folder_ready = False
            open_btn.setEnabled(ready)
            folder_btn.setEnabled(folder_ready)
            open_btn.clicked.connect(lambda _=False, i=index: self._download_open_path(i))
            folder_btn.clicked.connect(lambda _=False, i=index: self._download_show_folder(i))
            row_layout.addWidget(open_btn)
            row_layout.addWidget(folder_btn)
            item.setSizeHint(row_widget.sizeHint())
            self.download_tray_list.setItemWidget(item, row_widget)
        self.download_tray_hint.setText(f"{len(rows)} download(s) · {completed} completed · Open / Show folder available for completed files")

    def act(self, text, keys, slot, checkable=False):
        a = QAction(text, self)
        if keys:
            a.setShortcuts([QKeySequence(k) for k in ([keys] if isinstance(keys, str) else keys)])
        a.setCheckable(checkable)
        a.triggered.connect(lambda *_: slot())
        self.addAction(a)
        return a

    def _build_actions(self):
        A = self.act
        self.a_newtab = A("New tab", "Ctrl+T", lambda: self.add_tab(NEWTAB_URL))
        self.a_closetab = A("Close tab", "Ctrl+W", lambda: self.close_tab(self.tabbar.currentIndex()))
        self.a_reopen = A("Reopen closed tab", "Ctrl+Shift+T", self.reopen_tab)
        self.a_newwin = A("New window", "Ctrl+N", lambda: self.ctx.open_window(self.pd))
        self.a_incog = A("New Incognito window", "Ctrl+Shift+N", lambda: self.ctx.open_window(self.ctx.get_incognito()))
        self.a_openfile = A("Open file...", "Ctrl+O", self.open_file)
        self.a_save = A("Save page as...", "Ctrl+S", lambda: self._page_action(QWebEnginePage.WebAction.SavePage))
        self.a_pdf = A("Save page as PDF...", "Ctrl+P", self.print_pdf)
        self.a_find = A("Find in page...", "Ctrl+F", self.open_find)
        self.a_zin = A("Zoom in", ["Ctrl++", "Ctrl+="], lambda: self.zoom(+0.1))
        self.a_zout = A("Zoom out", "Ctrl+-", lambda: self.zoom(-0.1))
        self.a_zreset = A("Reset zoom", "Ctrl+0", lambda: self.zoom(0))
        self.a_full = A("Full screen", "F11", self.toggle_fullscreen)
        self.a_dev = A("Developer tools", ["F12", "Ctrl+Shift+I"], self.toggle_devtools)
        self.a_src = A("View page source", "Ctrl+U", lambda: self.view_source(None))
        self.a_bmbar = A("Show bookmarks bar", "Ctrl+Shift+B", self.toggle_bmbar, True)
        self.a_bmbar.setChecked(bool(self.cfg["show_bookmarks_bar"]))
        self.a_bookmark = A("Bookmark this page", "Ctrl+D", self.toggle_bookmark)
        self.a_bms = A("Bookmarks...", "Ctrl+Shift+O", self.show_bookmarks)
        self.a_hist = A("History...", "Ctrl+H", self.show_history)
        self.a_dl = A("Downloads...", "Ctrl+J", self.show_downloads)
        self.a_pw = A("Passwords...", None, self.show_passwords)
        self.a_fill = A("Autofill password", "Ctrl+Shift+L", lambda: self.maybe_autofill(self.current_tab(), force=True))
        self.a_ext = A("Extensions...", None, self.show_extensions)
        self.a_adblock = A("AdBlock settings", None, self.show_adblock)
        self.a_rightclick = A("Force Right Click", None, self.toggle_right_click, True)
        self.a_save_images = A("Save all pictures...", None, self.save_all_pictures)
        self.a_screenshot = A("Capture screenshot...", None, self.capture_screenshot)
        self.a_reader = A("Reader mode", None, self.reader_mode)
        self.a_ocr = A("OCR: extract text from images / PDF", None, self.open_ocr)
        self.a_bgremove = A("AI Background Remover", None, self.open_background_remover)
        self.a_calculator = A("Standard calculator", None, self.open_calculator)
        self.a_b64_decode = A("Base64 Decoder (D64)", None, self.open_base64_decoder)
        self.a_b64_encode = A("Base64 Encoder (E64)", None, self.open_base64_encoder)
        self.a_music = A("Music Player (🎵)", None, self.open_music_player)
        self.a_game_hub = A("Game Hub (🎮)", None, self.open_game_hub)
        self.a_media_diagnostics = A("Video / Media diagnostics...", None, self.open_media_diagnostics)
        self.a_permissions = A("Website permissions...", None, self.show_permissions)
        self.a_tabgroup = A("Set tab group...", None, self.set_tab_group)
        self.a_suspend = A("Suspend inactive tabs", None, self.suspend_inactive_tabs)
        self.a_autosuspend = A("Automatic Tab Suspend interval...", None, self.set_auto_suspend)
        self.a_set = A("Settings", "Ctrl+,", self.show_settings)
        self.a_about = A("About Neutron", None, self.show_about)
        self.a_quit = A("Quit", "Ctrl+Shift+Q", self.ctx.quit_all)
        A("Focus address bar", ["Ctrl+L", "F6", "Alt+D"], self.focus_url)
        A("Back", "Alt+Left", self.go_back)
        A("Forward", "Alt+Right", self.go_forward)
        A("Reload", ["F5", "Ctrl+R"], lambda: self._page_action(QWebEnginePage.WebAction.Reload))
        A("Hard reload", ["Ctrl+Shift+R", "Ctrl+F5"], lambda: self._page_action(QWebEnginePage.WebAction.ReloadAndBypassCache))
        A("Home", "Alt+Home", self.go_home)
        A("Next tab", "Ctrl+Tab", lambda: self.cycle_tab(+1))
        A("Previous tab", "Ctrl+Shift+Tab", lambda: self.cycle_tab(-1))
        for n in range(1, 10):
            A(f"Tab {n}", f"Ctrl+{n}", partial(self.goto_tab, n))

    def _build_menu(self):
        m = QMenu(self)
        self.btn_menu.setMenu(m)
        for a in (self.a_newtab, self.a_newwin, self.a_incog):
            m.addAction(a)
        self.menu_profiles = m.addMenu("Profiles")
        self.menu_profiles.aboutToShow.connect(self.populate_profiles)
        m.addSeparator()
        for a in (self.a_bookmark, self.a_bms, self.a_hist, self.a_dl, self.a_pw, self.a_fill, self.a_ext,
                  self.a_adblock, self.a_rightclick, self.a_save_images, self.a_screenshot, self.a_reader,
                  self.a_ocr, self.a_bgremove, self.a_calculator, self.a_b64_decode, self.a_b64_encode,
                  self.a_music, self.a_game_hub, self.a_media_diagnostics, self.a_permissions, self.a_tabgroup, self.a_suspend, self.a_autosuspend):
            m.addAction(a)
        m.addSeparator()
        zm = m.addMenu("Zoom")
        for a in (self.a_zin, self.a_zout, self.a_zreset):
            zm.addAction(a)
        for a in (self.a_find, self.a_openfile, self.a_save, self.a_pdf, self.a_full, self.a_bmbar):
            m.addAction(a)
        m.addSeparator()
        for a in (self.a_dev, self.a_src, self.a_set, self.a_about, self.a_quit):
            m.addAction(a)

    def apply_theme(self):
        self.setStyleSheet(build_qss("incognito" if self.pd.incognito else self.cfg["theme"]))

    # ---------- profiles menu ----------
    def populate_profiles(self):
        m = self.menu_profiles
        m.clear()
        for name in self.ctx.list_profiles():
            a = m.addAction(name)
            a.setCheckable(True)
            a.setChecked(name == self.pd.name and not self.pd.incognito)
            a.triggered.connect(lambda *_, n=name: self.ctx.open_window(self.ctx.get_profile(n)))
        m.addSeparator()
        m.addAction("New profile...", self.new_profile)
        m.addAction("Delete profile...", self.delete_profile)

    def new_profile(self):
        name, ok = QInputDialog.getText(self, "New profile", "Profile name:")
        name = safe_name(name) if ok and name.strip() else ""
        if name:
            self.ctx.open_window(self.ctx.get_profile(name))

    def delete_profile(self):
        names = [n for n in self.ctx.list_profiles() if n not in self.ctx.open_profile_names()]
        if not names:
            QMessageBox.information(self, APP_NAME, "No deletable profiles (profiles in use cannot be deleted).")
            return
        name, ok = QInputDialog.getItem(self, "Delete profile", "Select profile (ALL its data will be erased):", names, 0, False)
        if ok and QMessageBox.warning(self, APP_NAME, f"Delete profile '{name}' permanently?",
                                      QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No) == QMessageBox.StandardButton.Yes:
            self.ctx.delete_profile(name)

    # ---------- tabs ----------
    def current_tab(self) -> Optional[BrowserTab]:
        w = self.stack.currentWidget()
        return w if isinstance(w, BrowserTab) else None

    def add_tab(self, url: Optional[QUrl] = None, background: bool = False) -> BrowserTab:
        tab = BrowserTab(self, self.pd.profile)
        view, page = tab.view, tab.view.page()
        view.setZoomFactor(self.cfg["default_zoom"] / 100)
        self.stack.addWidget(tab)
        idx = self.tabbar.addTab("New Tab")
        close = QToolButton()
        close.setObjectName("tabclose")
        close.setText("✕")
        close.clicked.connect(lambda *_: self.close_tab_obj(tab))
        self.tabbar.setTabButton(idx, QTabBar.ButtonPosition.RightSide, close)
        page.titleChanged.connect(partial(self.on_title, tab))
        page.iconChanged.connect(partial(self.on_icon, tab))
        page.urlChanged.connect(partial(self.on_url, tab))
        page.loadStarted.connect(partial(self.on_load_started, tab))
        page.loadProgress.connect(partial(self.on_progress, tab))
        page.loadFinished.connect(partial(self.on_load_finished, tab))
        page.linkHovered.connect(lambda u: self.statusBar().showMessage(u))
        page.fullScreenRequested.connect(self.on_fullscreen)
        page.windowCloseRequested.connect(partial(self.close_tab_obj, tab))
        page.authenticationRequired.connect(self.on_auth)
        page.renderProcessTerminated.connect(partial(self.on_crash, tab))
        if hasattr(page, "permissionRequested"):  # Qt >= 6.8
            page.permissionRequested.connect(self.on_permission)
        elif hasattr(page, "featurePermissionRequested"):
            page.featurePermissionRequested.connect(partial(self.on_feature_permission, page))
        if not background:
            self.tabbar.setCurrentIndex(idx)
        if url is not None:
            view.load(url)
        if not self.pd.incognito:
            self._save_session_snapshot()
        return tab

    def tab_index(self, tab) -> int:
        return self.stack.indexOf(tab)

    def close_tab_obj(self, tab):
        i = self.tab_index(tab)
        if i >= 0:
            self.close_tab(i)

    def close_tab(self, i: int):
        tab = self.stack.widget(i)
        if not isinstance(tab, BrowserTab):
            return
        u = tab.view.url()
        if not self.pd.incognito and u.scheme() in ("http", "https", "file"):
            self.closed_tabs.append(u.toString())
        self.stack.removeWidget(tab)
        self.tabbar.removeTab(i)
        tab.dispose()
        if not self.pd.incognito:
            self._save_session_snapshot()
        if self.stack.count() == 0:
            self.close()

    def reopen_tab(self):
        if self.closed_tabs:
            self.add_tab(QUrl(self.closed_tabs.pop()))

    def on_tab_changed(self, i):
        if 0 <= i < self.stack.count():
            self.stack.setCurrentIndex(i)
            tab = self.current_tab()
            if tab:
                tab.last_activated = time.time()
            if tab and tab.suspended:
                self._set_tab_lifecycle(tab, "Active")
            self.sync_ui()
            self._sync_tool_buttons()

    def on_tab_moved(self, f, t):
        w = self.stack.widget(f)
        if w is not None:
            self.stack.removeWidget(w)
            self.stack.insertWidget(t, w)
            self.stack.setCurrentIndex(self.tabbar.currentIndex())
            pinned_count = sum(
                1 for i in range(self.stack.count())
                if isinstance(self.stack.widget(i), BrowserTab) and self.stack.widget(i).pinned
            )
            desired = min(t, max(0, pinned_count - 1)) if w.pinned else max(t, pinned_count)
            desired = max(0, min(desired, self.tabbar.count() - 1))
            if desired != t:
                # A second tabMoved event settles immediately because the tab
                # is now in the allowed pinned/unpinned partition.
                self.tabbar.moveTab(t, desired)
            if not self.pd.incognito:
                self._save_session_snapshot()

    def cycle_tab(self, d):
        n = self.tabbar.count()
        if n:
            self.tabbar.setCurrentIndex((self.tabbar.currentIndex() + d) % n)

    def goto_tab(self, n):
        c = self.tabbar.count()
        if c:
            self.tabbar.setCurrentIndex(c - 1 if n == 9 else min(n - 1, c - 1))

    # ---------- page signal handlers ----------
    def on_title(self, tab, title):
        i = self.tab_index(tab)
        if i < 0:
            return
        text = title or tab.view.url().toString() or "New Tab"
        if tab.group:
            text = f"[{tab.group}] {text}"
        if tab.muted:
            text = "🔇 " + text
        if tab.pinned:
            text = "📌 " + text
        self.tabbar.setTabText(i, text)
        self.tabbar.setTabToolTip(i, text)
        if tab is self.current_tab():
            self.update_window_title()

    def on_icon(self, tab, icon):
        i = self.tab_index(tab)
        if i >= 0:
            self.tabbar.setTabIcon(i, icon)

    def on_url(self, tab, url):
        if tab is self.current_tab():
            if not self.urlbar.hasFocus():
                self.set_url_text(url)
            self.update_star()
            self.update_nav()
        self._save_session_snapshot()

    def _save_session_snapshot(self):
        if self.pd.incognito:
            return
        timer = getattr(self, "_snap_timer", None)
        if timer is None:
            timer = self._snap_timer = QTimer(self)
            timer.setSingleShot(True)
            timer.timeout.connect(self._save_session_snapshot_now)
        timer.start(2000)

    def _save_session_snapshot_now(self):
        if self.pd.incognito:
            return
        tabs = []
        for i in range(self.stack.count()):
            item = self.stack.widget(i)
            if isinstance(item, BrowserTab):
                tabs.append({
                    "url": session_url(item.view.url()),
                    "group": item.group,
                    "pinned": bool(item.pinned),
                    "muted": bool(item.muted),
                })
        self.pd.save_session(tabs)

    def on_load_started(self, tab):
        tab.loading, tab.progress = True, 0
        if tab is self.current_tab():
            self.sync_ui()

    def on_progress(self, tab, p):
        tab.progress = p
        if tab is self.current_tab():
            self.progress.setValue(p)
            self.load_label.setText(f"Loading... {p}%")

    def on_load_finished(self, tab, ok):
        tab.loading = False
        try:
            url = tab.view.url()
            if ok and self.pd.history and url.scheme() in ("http", "https", "file") and url.host().lower() not in (OCR_HOST, BG_HOST):
                self.pd.history.add(url.toString(), tab.view.title())
            if ok:
                tab.crash_retries = 0
                self.maybe_autofill(tab)
                self.apply_page_tools(tab)
        except RuntimeError:
            return
        if tab is self.current_tab():
            self.sync_ui()
            if not ok:
                self.statusBar().showMessage("Failed to load page", 4000)
        if not self.pd.incognito:
            self._save_session_snapshot()

    def on_crash(self, tab, status, code):
        tab.crash_retries = getattr(tab, "crash_retries", 0) + 1
        try:
            url = tab.view.url()
            host = (url.host() or "").lower()
            log.error("Renderer terminated: status=%s exit_code=%s url=%s retries=%s",
                      status, code, url.toString(), tab.crash_retries)
        except Exception:
            host = ""
            log.exception("Could not record renderer crash details")
        # The known Dek-D novel reader is handled in per-page compatibility mode.
        # Do not automatically reload it after a renderer crash: repeated automatic
        # restarts can create a crash loop and make the whole browser appear hung.
        if host == "novel.dek-d.com" or host.endswith(".novel.dek-d.com"):
            self.statusBar().showMessage(
                "Dek-D renderer crashed. Compatibility mode was applied; press Reload manually if needed.", 9000
            )
            return
        self.statusBar().showMessage("The page renderer stopped; recovery attempt...", 4000)
        if tab.crash_retries <= 1:
            QTimer.singleShot(900, tab.view.reload)
        else:
            self.statusBar().showMessage("Page repeatedly crashed. Use Reload to retry manually. See neutron.log.", 9000)

    def on_fullscreen(self, req):
        req.accept()
        self._set_browser_fullscreen(bool(req.toggleOn()))

    def _set_browser_fullscreen(self, enabled):
        enabled = bool(enabled)
        if enabled == self.isFullScreen() and enabled == getattr(self, "_neutron_fullscreen", False):
            return
        if enabled:
            self._findbar_was_visible = self.findbar.isVisible()
            self._neutron_fullscreen = True
            self.chrome.hide()       # hides Tab Bar, URL Bar, bookmarks and every toolbar button
            self.findbar.hide()
            self.statusBar().hide()
            self.showFullScreen()
        else:
            self._neutron_fullscreen = False
            self.showNormal()
            self.chrome.show()
            self.statusBar().show()
            if getattr(self, "_findbar_was_visible", False):
                self.findbar.show()

    def toggle_fullscreen(self):
        self._set_browser_fullscreen(not self.isFullScreen())

    def on_auth(self, url, auth):
        user, ok = QInputDialog.getText(self, "Authentication required", f"{url.host()}\n{auth.realm()}\n\nUsername:")
        if not ok:
            return
        pw, ok = QInputDialog.getText(self, "Authentication required", "Password:", QLineEdit.EchoMode.Password)
        if ok:
            auth.setUser(user)
            auth.setPassword(pw)

    def on_permission(self, perm):  # Qt >= 6.8
        try:
            kind = getattr(perm.permissionType(), "name", str(perm.permissionType()))
            origin = perm.origin().toString()
            remembered = self.pd.permission_decision(origin, kind)
            if remembered is not None:
                perm.grant() if remembered else perm.deny()
                return
            box = QMessageBox(self)
            box.setWindowTitle("Website permission")
            box.setText(f"{perm.origin().host()} requests: {kind}")
            allow = box.addButton("Allow once", QMessageBox.ButtonRole.AcceptRole)
            deny = box.addButton("Block once", QMessageBox.ButtonRole.RejectRole)
            always = box.addButton("Always allow", QMessageBox.ButtonRole.YesRole)
            never = box.addButton("Always block", QMessageBox.ButtonRole.NoRole)
            box.exec()
            clicked = box.clickedButton()
            if clicked in (allow, always): perm.grant()
            else: perm.deny()
            if clicked in (always, never): self.pd.save_permission(origin, kind, clicked is always)
        except Exception:
            log.exception("permission")
            try: perm.deny()
            except Exception: pass

    def on_feature_permission(self, page, origin, feature):  # Qt < 6.8
        try:
            kind, key = feature.name, origin.toString()
            remembered = self.pd.permission_decision(key, kind)
            if remembered is None:
                box = QMessageBox(self)
                box.setWindowTitle("Website permission")
                box.setText(f"{origin.host()} requests: {kind}")
                once = box.addButton("Allow once", QMessageBox.ButtonRole.AcceptRole)
                box.addButton("Block once", QMessageBox.ButtonRole.RejectRole)
                always = box.addButton("Always allow", QMessageBox.ButtonRole.YesRole)
                never = box.addButton("Always block", QMessageBox.ButtonRole.NoRole)
                box.exec()
                clicked = box.clickedButton()
                remembered = clicked in (once, always)
                if clicked in (always, never):
                    self.pd.save_permission(key, kind, clicked is always)
            policy = QWebEnginePage.PermissionPolicy.PermissionGrantedByUser if remembered else QWebEnginePage.PermissionPolicy.PermissionDeniedByUser
            page.setFeaturePermission(origin, feature, policy)
        except Exception:
            log.exception("feature permission")

    # ---------- new window / popup ----------
    def create_page_for(self, wtype, profile):
        WT = QWebEnginePage.WebWindowType
        if wtype == WT.WebDialog:
            pop = PopupWindow(self, profile)
            pop.show()
            return pop.view.page()
        if wtype == WT.WebBrowserWindow:
            w = self.ctx.open_window(self.pd, blank=True)
            return w.add_tab(None).view.page()
        return self.add_tab(None, background=(wtype == WT.WebBrowserBackgroundTab)).view.page()

    # ---------- UI sync ----------
    def set_url_text(self, url: QUrl):
        hide = (url.isEmpty() or url.scheme() in ("neutron", "about")
                or url.host().lower() in (OCR_HOST, BG_HOST))
        self.urlbar.setText("" if hide else url.toString())
        self.urlbar.setCursorPosition(0)
        s = url.scheme()
        self.lock.setText("🔒" if s == "https" else "⚠" if s == "http" else "ⓘ")
        self.lock.setToolTip({"https": "Secure connection", "http": "Not secure"}.get(s, ""))

    def update_star(self):
        t = self.current_tab()
        on = bool(t) and self.pd.bookmarks.contains(t.view.url().toString())
        self.btn_star.setText("★" if on else "☆")

    def update_nav(self):
        t = self.current_tab()
        if t:
            h = t.view.history()
            self.btn_back.setEnabled(h.canGoBack())
            self.btn_fwd.setEnabled(h.canGoForward())

    def update_window_title(self):
        t = self.current_tab()
        title = (t.view.title() if t else "") or "New Tab"
        tag = " [Incognito]" if self.pd.incognito else (f" [{self.pd.name}]" if self.pd.name != "Default" else "")
        self.setWindowTitle(f"{title} - {APP_NAME}{tag}")

    def sync_ui(self):
        t = self.current_tab()
        if not t:
            return
        self.set_url_text(t.view.url())
        self.update_star()
        self.update_nav()
        self.update_window_title()
        self.btn_reload.setText("✕" if t.loading else "↻")
        self.btn_reload.setToolTip("Stop" if t.loading else "Reload (F5)")
        self.progress.setVisible(t.loading)
        self.progress.setValue(t.progress)
        self.load_label.setText(f"Loading... {t.progress}%" if t.loading else "")
        z = round(t.view.zoomFactor() * 100)
        if z != 100:
            self.statusBar().showMessage(f"Zoom {z}%", 1500)

    def eventFilter(self, obj, ev):
        if obj is getattr(self, "download_tray", None) and ev.type() == QEvent.Type.Hide:
            timer = getattr(self, "download_tray_timer", None)
            if timer is not None:
                timer.stop()
        if obj is self.urlbar and ev.type() == QEvent.Type.FocusIn:
            now = time.monotonic()
            if self.pd.history and now - getattr(self, "_comp_ts", 0.0) > 30:
                self._comp_ts = now
                urls = self.pd.history.recent_urls() + [b["url"] for b in self.pd.bookmarks.items]
                self.comp_model.setStringList(list(dict.fromkeys(urls)))
            if ev.reason() == Qt.FocusReason.MouseFocusReason:
                QTimer.singleShot(0, self.urlbar.selectAll)
        return super().eventFilter(obj, ev)

    # ---------- navigation ----------
    def navigate(self, text):
        url = smart_url(text, self.cfg)
        t = self.current_tab()
        if t is None:
            self.add_tab(url)
        else:
            t.view.load(url)
            t.view.setFocus()

    def _page_action(self, action):
        t = self.current_tab()
        if t:
            t.view.page().triggerAction(action)

    def go_back(self):
        t = self.current_tab()
        t and t.view.back()

    def go_forward(self):
        t = self.current_tab()
        t and t.view.forward()

    def reload_or_stop(self):
        t = self.current_tab()
        if t:
            t.view.stop() if t.loading else t.view.reload()

    def go_home(self):
        self.navigate(self.cfg["homepage"])

    def focus_url(self):
        self.urlbar.setFocus()
        self.urlbar.selectAll()

    def open_file(self):
        p, _ = QFileDialog.getOpenFileName(self, "Open file")
        if p:
            self.navigate(QUrl.fromLocalFile(p).toString())

    def view_source(self, view):
        v = view or (self.current_tab().view if self.current_tab() else None)
        if v and v.url().scheme() in ("http", "https", "file"):
            self.add_tab(QUrl("view-source:" + v.url().toString()))

    def print_pdf(self):
        t = self.current_tab()
        if not t:
            return
        name = re.sub(r'[\\/:*?"<>|]', "_", t.view.title() or "page")[:80]
        path, _ = QFileDialog.getSaveFileName(self, "Save as PDF", name + ".pdf", "PDF (*.pdf)")
        if path:
            t.view.page().printToPdf(path)
            self.statusBar().showMessage("Saving PDF...", 3000)

    def zoom(self, delta):
        t = self.current_tab()
        if not t:
            return
        z = self.cfg["default_zoom"] / 100 if delta == 0 else max(0.25, min(5.0, t.view.zoomFactor() + delta))
        t.view.setZoomFactor(z)
        self.statusBar().showMessage(f"Zoom {round(z * 100)}%", 1500)

    def toggle_devtools(self):
        t = self.current_tab()
        t and t.toggle_devtools()

    # ---------- find ----------
    def open_find(self):
        self.findbar.show()
        self.find_edit.setFocus()
        self.find_edit.selectAll()

    def close_find(self):
        self.findbar.hide()
        t = self.current_tab()
        if t:
            t.view.page().findText("")
            t.view.setFocus()

    def find(self, text, backward):
        t = self.current_tab()
        if t:
            t.view.page().findText(text, QWebEnginePage.FindFlag.FindBackward) if backward else t.view.page().findText(text)

    # ---------- bookmarks ----------
    def toggle_bookmark(self):
        t = self.current_tab()
        if t and t.view.url().scheme() in ("http", "https", "file"):
            self.pd.bookmarks.toggle(t.view.title(), t.view.url().toString())
            self.update_star()

    def toggle_bmbar(self):
        on = self.a_bmbar.isChecked()
        self.bmbar.setVisible(on)
        self.cfg["show_bookmarks_bar"] = on
        self.cfg.save()

    def refresh_bookmarks_bar(self):
        while self.bm_layout.count():
            it = self.bm_layout.takeAt(0)
            if it.widget():
                it.widget().deleteLater()
        for b in self.pd.bookmarks.items:
            btn = QToolButton()
            title = b["title"] or b["url"]
            btn.setText(title[:22] + ("…" if len(title) > 22 else ""))
            btn.setToolTip(b["url"])
            btn.clicked.connect(lambda *_, u=b["url"]: self.navigate(u))
            btn.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
            btn.customContextMenuRequested.connect(partial(self._bm_menu, b["url"], btn))
            self.bm_layout.addWidget(btn)
        self.bm_layout.addStretch()
        self.update_star()

    def _bm_menu(self, url, btn, pos):
        m = QMenu(self)
        m.addAction("Open in new tab", lambda: self.add_tab(QUrl(url)))
        m.addAction("Remove", lambda: self.pd.bookmarks.remove(url))
        m.exec(btn.mapToGlobal(pos))

    # ---------- passwords ----------
    def on_credentials_captured(self, page, payload):
        v = self.pd.vault
        if not (v and v.available() and self.cfg["save_passwords"]):
            return
        d = json.loads(payload)
        origin, user, pw = d.get("o", ""), d.get("u", ""), d.get("p", "")
        page_url = page.url()
        # Do not save credentials from clear-text HTTP pages.
        if page_url.scheme().lower() != "https" or not pw or origin != origin_of(page_url):
            return
        key = (origin, user, pw)
        if self._last_cred[0] == key and time.time() - self._last_cred[1] < 4:
            return
        self._last_cred = (key, time.time())
        QTimer.singleShot(0, partial(self.offer_save, origin, user, pw))

    def offer_save(self, origin, user, pw):
        v = self.pd.vault
        if v.unlocked() and any(e["u"] == user and e["p"] == pw for e in v.find(origin)):
            return
        box = QMessageBox(self)
        box.setWindowTitle("Save password?")
        box.setText(f"Save password for <b>{html.escape(user or '(no username)')}</b> on {html.escape(origin)}?")
        save = box.addButton("Save", QMessageBox.ButtonRole.AcceptRole)
        box.addButton("Not now", QMessageBox.ButtonRole.RejectRole)
        box.exec()
        if box.clickedButton() is save and unlock_vault_ui(self, v):
            v.save_entry(origin, user, pw)
            self.statusBar().showMessage("Password saved", 3000)

    def maybe_autofill(self, tab, force=False):
        v = self.pd.vault
        if not tab or not (v and v.available() and (self.cfg["save_passwords"] or force)):
            return
        page_url = tab.view.url()
        # Autofill is restricted to HTTPS origins to avoid leaking credentials over HTTP.
        origin = origin_of(page_url) if page_url.scheme().lower() == "https" else ""
        if origin:
            tab.view.page().runJavaScript(PROBE_JS, partial(self._autofill_probe, tab, origin, force))

    def _autofill_probe(self, tab, origin, force, has):
        try:
            v = self.pd.vault
            if not has:
                return
            if not v.unlocked():
                if v.prompted and not force:
                    return
                v.prompted = True
                if not unlock_vault_ui(self, v):
                    return
            if origin not in v.origins():
                return
            entries = v.find(origin)
            if entries:
                e = entries[-1]
                tab.view.page().runJavaScript(FILL_JS % (json.dumps(e["u"]), json.dumps(e["p"])))
        except RuntimeError:
            pass

    # ---------- dialogs ----------
    def _show(self, dlg):
        dlg.show()
        return dlg

    def show_bookmarks(self):
        bm = self.pd.bookmarks
        self._show(ListDialog(self, "Bookmarks", ["Title", "URL"], lambda q: [(b["url"], [b["title"], b["url"]]) for b in bm.items],
                              on_open=lambda k: self.navigate(k[0]), on_delete=lambda ks: [bm.remove(k) for k in ks]))

    def show_history(self):
        h = self.pd.history
        if not h:
            QMessageBox.information(self, APP_NAME, "History is not recorded in Incognito mode.")
            return
        self._show(ListDialog(self, "History", ["Title", "URL", "Visited"],
                              lambda q: [(r[0], [r[1] or "", r[2], time.strftime("%Y-%m-%d %H:%M", time.localtime(r[3]))]) for r in h.search(q)],
                              on_open=lambda ids: None, on_delete=h.delete, on_clear=h.clear, searchable=True, widths=(280, 380)))
        d = self.findChildren(ListDialog)[-1]
        d.on_open = lambda ids: self.navigate(next((r[2] for r in h.search(d.search.text()) if r[0] == ids[0]), ""))

    def show_downloads(self):
        dm = self.ctx.downloads

        def open_file(ks):
            if ks:
                QDesktopServices.openUrl(QUrl.fromLocalFile(dm.path_of(ks[0])))

        def open_dir(ks):
            if ks:
                QDesktopServices.openUrl(QUrl.fromLocalFile(os.path.dirname(dm.path_of(ks[0]))))

        def cancel(ks):
            for k in ks:
                dm.cancel(k)

        def pause(ks):
            for k in ks:
                try: dm.items[k].pause()
                except (RuntimeError, AttributeError): pass

        def resume(ks):
            for k in ks:
                try: dm.items[k].resume()
                except (RuntimeError, AttributeError): pass

        def clear():
            S = QWebEngineDownloadRequest.DownloadState
            kept = []
            for request in dm.items:
                if dm.meta.get(id(request), {}).get("queued"):
                    kept.append(request)
                    continue
                try:
                    if request.state() == S.DownloadInProgress:
                        kept.append(request)
                except RuntimeError:
                    continue
            dm.items = kept

        self._show(ListDialog(self, "Downloads", ["File", "Category", "Progress", "Speed", "Status"], dm.rows, on_open=open_file, on_clear=clear,
                              extras=[("Show in folder", open_dir), ("Pause", pause), ("Resume", resume), ("Cancel", cancel)], interval=700, widths=(300, 280)))

    # ---------- AdBlock / website permissions / power tools ----------
    def _current_site_host(self):
        tab = self.current_tab()
        return tab.view.url().host().lower() if tab else ""

    def _sync_tool_buttons(self):
        tab = self.current_tab()
        if tab:
            self.btn_rightclick.setText("🖱✓" if tab.view.force_right_click else "🖱")
            self.a_rightclick.setChecked(tab.view.force_right_click)
        host = self._current_site_host()
        blocked = self.pd.adblock.blocked_count
        self.btn_shields.setToolTip(f"AdBlock: {blocked} blocked requests | {host or 'No site'}")

    def show_adblock(self):
        manager = self.pd.adblock
        host = self._current_site_host()
        dlg = QDialog(self)
        dlg.setWindowTitle("Neutron AdBlock / Privacy Shield")
        dlg.resize(560, 330)
        layout = QVBoxLayout(dlg)
        enabled = QCheckBox("Enable network ad and tracker blocking for this profile")
        enabled.setChecked(manager.enabled)
        layout.addWidget(enabled)
        summary = QLabel(f"Loaded network rules: {manager.rules_count():,}    Blocked requests this session: {manager.blocked_count:,}")
        layout.addWidget(summary)
        engine_note = manager.engine_name
        status = QLabel(f"Filter lists: AdGuard Base + AdGuard Tracking Protection. Engine: {engine_note}. Indexed matching is built in a worker; main-frame navigation and state-changing requests are allowed. Advanced scriptlet rules are not supported by the built-in CSS/network subset.")
        status.setWordWrap(True)
        layout.addWidget(status)
        compat_note = QLabel(
            "Compatibility note: Search engines (Google, Bing, DuckDuckGo, Brave Search, Yahoo and Ecosia) "
            "are automatically excluded from network and filter-list cosmetic blocking to keep search fast and reliable. "
            "If another website is slow or broken, Allowlist it or disable AdBlock temporarily."
        )
        compat_note.setWordWrap(True)
        layout.addWidget(compat_note)
        site = QLabel(f"Current site: {host or 'No website'}")
        layout.addWidget(site)
        row = QHBoxLayout()
        whitelist = QPushButton("Remove from Allowlist" if host in manager.whitelist else "Allow this website")
        whitelist.setEnabled(bool(host))
        update = QPushButton("Update filter lists")
        blocked = QPushButton("Recent blocked requests")
        elements = QPushButton("Manage blocked elements")
        add_rule = QPushButton("Add / test rule...")
        pick_element = QPushButton("Pick element on page...")
        row.addWidget(whitelist); row.addWidget(update); layout.addLayout(row)
        row2 = QHBoxLayout()
        row2.addWidget(blocked); row2.addWidget(elements); row2.addWidget(add_rule); row2.addWidget(pick_element); row2.addStretch()
        layout.addLayout(row2)
        custom = QPushButton("Open custom filter rules file")
        reload_button = QPushButton("Reload custom/filter rules")
        close = QPushButton("Close")
        layout.addWidget(custom)
        layout.addWidget(reload_button)
        bottom = QHBoxLayout(); bottom.addStretch(); bottom.addWidget(close); layout.addLayout(bottom)

        def toggle_site():
            if not host: return
            if host in manager.whitelist: manager.remove_whitelist(host)
            else: manager.add_whitelist(host)
            whitelist.setText("Remove from Allowlist" if host in manager.whitelist else "Allow this website")
            tab = self.current_tab()
            if tab: tab.view.reload()
        def update_lists():
            update.setEnabled(False); update.setText("Updating...")
            worker = manager.update_lists(dlg)
            def done(ok, errors):
                try: manager.updateFinished.disconnect(done)
                except Exception: pass
                update.setEnabled(True); update.setText("Update filter lists")
                summary.setText(f"Loaded network rules: {manager.rules_count():,}    Blocked requests this session: {manager.blocked_count:,}")
                detail = f"Updated {ok} filter list(s)."
                if errors: detail += "\n" + errors
                QMessageBox.information(dlg, "AdBlock update", detail)
                if self.current_tab(): self.current_tab().view.reload()
            manager.updateFinished.connect(done)
            worker.start()
        def open_custom():
            manager.root.mkdir(parents=True, exist_ok=True)
            if not manager.custom_path.exists(): manager.custom_path.write_text("! Neutron custom network filters\n", encoding="utf-8")
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(manager.custom_path)))
        def show_blocked():
            def clear_recent():
                with manager._lock:
                    manager.recent_blocked.clear()
            def rows(query):
                with manager._lock:
                    snapshot = list(reversed(manager.recent_blocked))
                q = (query or "").lower()
                return [(i, list(item)) for i, item in enumerate(snapshot) if not q or q in " ".join(item).lower()]
            self._show(ListDialog(self, "Recently blocked requests (memory only)", ["Time", "Host", "Type"], rows,
                                  on_clear=clear_recent, searchable=True, widths=(100, 300)))
        def show_elements():
            def rows(query):
                q = (query or "").lower()
                items = []
                for site, selectors in manager.cosmetic.items():
                    for selector in selectors:
                        cols = [site, selector]
                        if not q or q in " ".join(cols).lower():
                            items.append(((site, selector), cols))
                return items
            def remove(keys):
                for site, selector in keys:
                    manager.remove_cosmetic(site, selector)
            self._show(ListDialog(self, "Blocked page elements", ["Website", "CSS selector"], rows,
                                  on_delete=remove, searchable=True, widths=(220, 520)))
        def reload_custom_rules():
            manager._compile_rules()
            self.statusBar().showMessage("AdBlock rules are compiling in the background", 3000)
        def on_adblock_toggled(value):
            if value and not manager.enabled:
                answer = QMessageBox.warning(
                    dlg, "Enable AdBlock?",
                    "AdBlock may slow down or break some websites. Search engines are exempted, "
                    "but other sites may still be affected. If a website behaves incorrectly, "
                    "add it to Allowlist or turn AdBlock off temporarily.\n\nEnable AdBlock?",
                    QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                    QMessageBox.StandardButton.No,
                )
                if answer != QMessageBox.StandardButton.Yes:
                    enabled.blockSignals(True); enabled.setChecked(False); enabled.blockSignals(False)
                    return
            self._set_adblock_enabled(value)
        enabled.toggled.connect(on_adblock_toggled)
        whitelist.clicked.connect(toggle_site)
        update.clicked.connect(update_lists)
        blocked.clicked.connect(show_blocked)
        elements.clicked.connect(show_elements)
        add_rule.clicked.connect(self.show_adblock_rule_editor)
        pick_element.clicked.connect(self.start_element_picker)
        custom.clicked.connect(open_custom)
        reload_button.clicked.connect(reload_custom_rules)
        close.clicked.connect(dlg.accept)
        dlg.exec()

    def show_adblock_rule_editor(self):
        manager = self.pd.adblock
        current_host = self._current_site_host()
        dlg = QDialog(self)
        dlg.setWindowTitle("Add / Test AdBlock Rule")
        dlg.resize(640, 390)
        layout = QVBoxLayout(dlg)
        form = QFormLayout()
        kind = QComboBox()
        kind.addItem("Hide element (CSS selector / HTML tag)", "cosmetic")
        kind.addItem("Block network URL / domain", "network")
        kind.addItem("Block image requests from domain", "image")
        scope = QComboBox()
        scope.addItem("Current website only", "site")
        scope.addItem("All websites", "all")
        scope.setCurrentIndex(0 if current_host else 1)
        editor = QPlainTextEdit()
        editor.setPlaceholderText("Examples: div.ad-banner   |   .sponsored   |   #popup\nOr a domain / URL for network blocking")
        editor.setFixedHeight(110)
        form.addRow("Rule type", kind)
        form.addRow("Scope", scope)
        form.addRow("Selector / URL / domain", editor)
        layout.addLayout(form)
        help_label = QLabel("CSS mode accepts Chromium CSS selectors: tags (div), classes (.ad), IDs (#banner), attributes and combinations. AdGuard extended selectors are not CSS and are rejected.")
        help_label.setWordWrap(True)
        layout.addWidget(help_label)
        result = QLabel("Enter a rule and choose Test or Save.")
        result.setWordWrap(True)
        layout.addWidget(result)
        buttons = QHBoxLayout()
        test = QPushButton("Test rule")
        save = QPushButton("Save rule")
        save.setObjectName("go")
        close = QPushButton("Close")
        buttons.addWidget(test); buttons.addWidget(save); buttons.addStretch(); buttons.addWidget(close)
        layout.addLayout(buttons)

        def normalized_rule():
            value = editor.toPlainText().strip()
            if not value:
                raise ValueError("Enter a CSS selector, URL, or domain first.")
            host_scope = current_host if scope.currentData() == "site" else "*"
            mode = kind.currentData()
            if mode == "cosmetic":
                if not _selector_is_chromium_css(value):
                    raise ValueError("Unsupported Chromium CSS selector. Remove AdGuard extended syntax.")
                if scope.currentData() == "site" and not current_host:
                    raise ValueError("There is no current website to scope this rule to.")
                return ("cosmetic", host_scope, value)

            if mode == "image":
                text = value.strip()
                if "://" in text:
                    parsed = QUrl.fromUserInput(text)
                    domain = parsed.host().lower()
                else:
                    domain = text.lower().strip().strip("/^")
                if not domain or any(ch in domain for ch in " /\\:*?"):
                    raise ValueError("Enter a valid image host/domain, e.g. images.example.com")
                network = f"||{domain}^$image"
            else:
                text = value.strip()
                if text.startswith(("||", "|", "*", "/")):
                    network = text
                else:
                    parsed = QUrl.fromUserInput(text if "://" in text else "https://" + text)
                    if not parsed.isValid() or not parsed.host():
                        raise ValueError("Enter a valid domain or HTTP/HTTPS URL.")
                    domain = parsed.host().lower()
                    path = parsed.path().strip("/")
                    network = f"||{domain}/{path}^" if path else f"||{domain}^"
            if scope.currentData() == "site":
                if not current_host:
                    raise ValueError("There is no current website to scope this rule to.")
                network += f",domain={current_host}" if "$" in network else f"$domain={current_host}"
            if not manager._parse_network_rule(network):
                raise ValueError("Neutron cannot parse this network rule. Check the URL/domain/options.")
            return ("network", "", network)

        def test_rule():
            try:
                mode, host, value = normalized_rule()
                if mode == "cosmetic":
                    tab = self.current_tab()
                    if not tab:
                        raise ValueError("Open a website before testing a CSS selector.")
                    selector_json = json.dumps(value)
                    tab.view.page().runJavaScript(
                        f"(function(){{try{{return {{ok:true,count:document.querySelectorAll({selector_json}).length}};}}catch(e){{return {{ok:false,error:String(e)}};}}}})()",
                        lambda data: result.setText(
                            f"Matched {data.get('count', 0)} element(s) on the current page." if isinstance(data, dict) and data.get("ok")
                            else f"Invalid CSS selector: {data.get('error', 'unknown error')}" if isinstance(data, dict)
                            else "Could not test selector on this page."
                        )
                    )
                else:
                    result.setText("Valid network rule: " + value + "\n" + ("Scoped to current website." if scope.currentData() == "site" else "Applies to all websites."))
            except Exception as exc:
                result.setText(f"Rule test failed: {type(exc).__name__}: {exc}")

        def save_rule():
            try:
                mode, host, value = normalized_rule()
                if mode == "cosmetic":
                    manager.add_cosmetic(host, value)
                else:
                    manager.add_network_rule(value)
                result.setText("Rule saved. Network rules are compiling in the background." if mode == "network" else "CSS rule saved and applied to this profile.")
                self.statusBar().showMessage("AdBlock rule saved", 3000)
            except Exception as exc:
                QMessageBox.warning(dlg, "Invalid AdBlock rule", f"{type(exc).__name__}: {exc}")

        test.clicked.connect(test_rule)
        save.clicked.connect(save_rule)
        close.clicked.connect(dlg.accept)
        dlg.exec()

    def _set_adblock_enabled(self, enabled):
        enabled = bool(enabled)
        self.cfg["adblock_enabled"] = enabled
        self.cfg["adblock_opt_in_acknowledged"] = True
        self.cfg.save()
        profiles = list(self.ctx.profiles.values()) + ([self.ctx.incognito_pd] if self.ctx.incognito_pd else [])
        for pd in profiles:
            if pd is not None:
                pd.adblock.enabled = enabled
                if enabled:
                    pd.adblock.start_enabled_engine()
                for window in list(self.ctx.windows):
                    if window.pd is pd:
                        for i in range(window.stack.count()):
                            tab = window.stack.widget(i)
                            if isinstance(tab, BrowserTab):
                                window.apply_page_tools(tab)
        self.statusBar().showMessage(
            "AdBlock enabled — reload pages to apply network filters" if enabled else "AdBlock disabled",
            4000,
        )

    def start_element_picker(self, view=None):
        view = view or (self.current_tab().view if self.current_tab() else None)
        if not view:
            return
        view.page().runJavaScript(ELEMENT_PICKER_JS)
        self.statusBar().showMessage("Element Picker: click an element to block it; press Esc to cancel", 5000)

    def on_element_selected(self, payload):
        try:
            data = json.loads(payload)
            host, selector = data.get("host", "").lower(), data.get("selector", "")
            if not host or not selector or len(selector) > 800:
                return
            answer = QMessageBox.question(self, "Block website element", f"Add a cosmetic blocking rule for:\n{host}\n\n{selector}\n\nThis rule is saved only for this profile.")
            if answer == QMessageBox.StandardButton.Yes:
                self.pd.adblock.add_cosmetic(host, selector)
                tab = self.current_tab()
                if tab and tab.view.url().host().lower() == host:
                    self.apply_page_tools(tab)
                self.statusBar().showMessage("Element blocking rule saved", 3000)
        except Exception:
            log.exception("element selection")

    def apply_page_tools(self, tab):
        try:
            tab.view.page().runJavaScript(
                RIGHT_CLICK_JS + f"\nwindow.__neutronForceRightClick={str(tab.view.force_right_click).lower()};"
            )
            host = tab.view.url().host().lower()
            if self.pd.adblock.enabled:
                list_selectors = self.pd.adblock.cosmetic_for(host)
                user_selectors = self.pd.adblock.user_cosmetic_for(host)
            else:
                list_selectors, user_selectors = [], []
            # Independent stylesheets: one invalid selector never cancels other rules.
            js = r'''(function(listSelectors,userSelectors){
              const invalid = s => !s || s.length > 800 || /\+js\(|#\?#|#%#|:has-text\(|:contains\(|:matches-css\(|:xpath\(|:-abp-/i.test(s);
              function apply(id,selectors){
                let el=document.getElementById(id);
                const usable=[...new Set(selectors||[])].filter(s=>!invalid(s));
                if(!usable.length){if(el)el.remove();return;}
                const root=document.head||document.documentElement;if(!root)return;
                if(!el){el=document.createElement('style');el.id=id;root.appendChild(el);}
                const sheet=el.sheet;if(!sheet)return;
                while(sheet.cssRules.length){try{sheet.deleteRule(0);}catch(_){break;}}
                usable.forEach(sel=>{try{sheet.insertRule(sel+'{display:none!important;visibility:hidden!important}',sheet.cssRules.length);}catch(_){/* skip only this selector */}});
              }
              apply('__neutron_list_cosmetics',listSelectors);
              apply('__neutron_user_cosmetics',userSelectors);
            })(''' + json.dumps(list_selectors, ensure_ascii=False) + ',' + json.dumps(user_selectors, ensure_ascii=False) + r''');'''
            tab.view.page().runJavaScript(js)
        except Exception:
            log.exception("apply page tools")

    def toggle_right_click(self):
        tab = self.current_tab()
        if not tab:
            return
        tab.view.force_right_click = not tab.view.force_right_click
        tab.view.page().runJavaScript(RIGHT_CLICK_JS + f"\nwindow.__neutronForceRightClick={str(tab.view.force_right_click).lower()};")
        self._sync_tool_buttons()
        self.statusBar().showMessage("Force Right Click ON" if tab.view.force_right_click else "Force Right Click OFF", 2500)

    def save_context_image(self, image_url):
        """Save one image from the image context menu using the browser downloader."""
        try:
            if not image_url or image_url.scheme().lower() not in ("http", "https"):
                QMessageBox.information(self, APP_NAME, "Only HTTP/HTTPS images can be saved.")
                return
            tab = self.current_tab()
            if not tab:
                return
            record = [{"url": image_url.toString(), "width": 0, "height": 0, "alt": "Context-menu image"}]
            self._image_records_ready(tab, record)
        except Exception as exc:
            log.exception("save context image")
            QMessageBox.warning(self, APP_NAME, f"Could not save image: {exc}")

    def save_all_pictures(self):
        tab = self.current_tab()
        if not tab:
            return
        choice, ok = QInputDialog.getItem(
            self, "Save All Pictures", "Image scan mode:",
            ["Current loaded content", "Auto-scroll to load lazy images"], 1, False
        )
        if not ok:
            return
        if choice == "Auto-scroll to load lazy images":
            tab.view.page().runJavaScript(
                "({x:window.scrollX,y:window.scrollY,h:document.documentElement.scrollHeight,v:window.innerHeight})",
                lambda d, t=tab: self._image_scroll_scan(t, d or {})
            )
        else:
            self._collect_page_images(tab)

    def _image_scroll_scan(self, tab, state):
        viewport = max(1, int(state.get("v", 700)))
        original = max(0, int(state.get("y", 0)))
        original_x = max(0, int(state.get("x", 0)))
        limit = 250  # bounded scan: prevent endless/infinite-scroll pages from running indefinitely
        visits = 0

        def finish():
            if not tab or not tab.view:
                return
            tab.view.page().runJavaScript(
                f"window.scrollTo({{left:{original_x},top:{original},behavior:'instant'}});true",
                lambda *_: QTimer.singleShot(300, lambda: self._collect_page_images(tab))
            )

        def step(target_y):
            nonlocal visits
            if not tab or not tab.view or visits >= limit:
                finish()
                return
            visits += 1
            js = f"window.scrollTo({{left:window.scrollX,top:{target_y},behavior:'instant'}});({{x:window.scrollX,y:window.scrollY,h:Math.max(document.documentElement.scrollHeight,document.body.scrollHeight),v:window.innerHeight}})"
            tab.view.page().runJavaScript(js, lambda d: after_step(d or {}, target_y))

        def after_step(data, target_y):
            actual_y = max(0, int(data.get("y", target_y)))
            height = max(0, int(data.get("h", 0)))
            vh = max(1, int(data.get("v", viewport)))
            if actual_y + vh >= height - 3:
                # Let lazy image/network handlers update document height once more before deciding to stop.
                QTimer.singleShot(450, lambda: recheck(actual_y, height, vh))
            else:
                QTimer.singleShot(180, lambda: step(actual_y + max(250, int(vh * 0.8))))

        def recheck(actual_y, previous_height, vh):
            if not tab or not tab.view:
                return
            tab.view.page().runJavaScript(
                "Math.max(document.documentElement.scrollHeight,document.body.scrollHeight)",
                lambda new_h: step(actual_y + max(250, int(vh * 0.8))) if int(new_h or 0) > previous_height + 3 else finish()
            )

        step(0)

    def _collect_page_images(self, tab):
        js = r'''(function(){
          const out=[],seen=new Set();
          function add(url,w,h,alt){
            if(out.length>=2500||!url||seen.has(url)||!/^https?:/i.test(url))return;
            seen.add(url);out.push({url:url,width:w||0,height:h||0,alt:alt||''});
          }
          document.querySelectorAll('img').forEach(i=>add(i.currentSrc||i.src,i.naturalWidth,i.naturalHeight,i.alt));
          document.querySelectorAll('*').forEach(e=>{
            if(out.length>=2500)return;
            const bg=getComputedStyle(e).backgroundImage;
            if(!bg||bg==='none')return;
            const r=e.getBoundingClientRect(),w=Math.round(r.width),h=Math.round(r.height);
            const re=/url\(["']?(.*?)["']?\)/g;let m;
            while((m=re.exec(bg))){try{add(new URL(m[1],location.href).href,w,h,'CSS background');}catch(e){}}
          });
          return out;
        })()'''
        tab.view.page().runJavaScript(
            js, lambda data, t=tab: self._image_records_ready(t, data or [])
        )

    def _image_records_ready(self, tab, records):
        if not records:
            QMessageBox.information(self, APP_NAME, "No downloadable HTTP/HTTPS images were found in the current page.")
            return
        # A defensive cap avoids creating an enormous dialog from pages that
        # generate unbounded image URLs (for example, infinite galleries).
        if len(records) > 2500:
            QMessageBox.information(self, "Save All Pictures", "This page exposed more than 2,500 images. The first 2,500 unique image URLs will be shown to keep the browser responsive.")
            records = records[:2500]
        dlg = ImageBatchDialog(self, records)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        chosen = dlg.selected_records()
        if not chosen:
            QMessageBox.information(self, APP_NAME, "No images selected.")
            return
        folder = QFileDialog.getExistingDirectory(self, "Select folder for downloaded pictures", self.cfg["download_dir"] or str(Path.home() / "Downloads"))
        if not folder:
            return
        def start(cookie):
            headers_ua = self.pd.profile.httpUserAgent()
            filters = {"min_kb": dlg.min_kb.value(), "max_kb": dlg.max_kb.value()}
            worker = ImageDownloadThread(chosen, folder, filters, tab.view.url().toString(), headers_ua, cookie or "", self.ctx.qt)
            self._image_worker = worker
            self.ctx.image_workers.add(worker)
            worker.progress.connect(lambda m: self._image_progress_message(m))
            worker.completed.connect(self._image_download_completed)
            worker.finished.connect(lambda w=worker: self.ctx.image_workers.discard(w))
            worker.finished.connect(worker.deleteLater)
            worker.start()
        tab.view.page().runJavaScript("document.cookie", start)

    def _image_progress_message(self, message_text):
        try:
            self.statusBar().showMessage(message_text, 2500)
        except RuntimeError:
            pass

    def _image_download_completed(self, saved, skipped, errors):
        try:
            QMessageBox.information(self, "Save All Pictures", f"Saved: {saved}\nSkipped/failed: {skipped}" + (f"\n\n{errors}" if errors else ""))
        except RuntimeError:
            log.info("Image download finished after its browser window closed: saved=%s skipped=%s", saved, skipped)

    def capture_screenshot(self):
        tab = self.current_tab()
        if not tab:
            return
        options = [
            "Visible area only (no scrolling)",
            "Full page (auto-scroll + stitch tiles)",
            "Full page (fast capture + instant scroll)",
        ]
        choice, ok = QInputDialog.getItem(self, "Screenshot mode", "Capture:", options, 1, False)
        if not ok: return
        fmt, ok = QInputDialog.getItem(self, "Image format", "Save as:", ["PNG", "JPG"], 0, False)
        if not ok: return
        jpg_quality = 92
        if fmt == "JPG":
            jpg_quality, ok = QInputDialog.getInt(self, "JPEG Quality", "Quality (1-100):", 92, 1, 100)
            if not ok: return
        self._screenshot_jpg_quality = jpg_quality
        suffix = ".png" if fmt == "PNG" else ".jpg"
        base = re.sub(r'[\\/:*?"<>|]', "_", tab.view.title() or "Neutron_Screenshot")[:80]
        path, _ = QFileDialog.getSaveFileName(self, "Save screenshot", base + suffix, "PNG (*.png);;JPEG (*.jpg *.jpeg)")
        if not path: return
        expected = ".png" if fmt == "PNG" else ".jpg"
        if Path(path).suffix.lower() not in ((".png",) if fmt == "PNG" else (".jpg", ".jpeg")):
            path += expected
        if choice == options[0]:
            image = tab.view.grab().toImage()
            if fmt == "JPG" and image.hasAlphaChannel():
                rgb = QImage(image.size(), QImage.Format.Format_RGB32); rgb.fill(QColor("white")); painter=QPainter(rgb); painter.drawImage(0,0,image); painter.end(); image=rgb
            if not image.save(path, "PNG" if fmt == "PNG" else "JPG", jpg_quality if fmt == "JPG" else -1):
                QMessageBox.warning(self, APP_NAME, "Could not write screenshot file.")
            else:
                self.statusBar().showMessage("Screenshot saved", 3000)
            return
        smooth_scroll = choice == options[1]
        tab.view.page().runJavaScript("({w:Math.max(document.documentElement.scrollWidth,document.body.scrollWidth),h:Math.max(document.documentElement.scrollHeight,document.body.scrollHeight),vw:window.innerWidth,vh:window.innerHeight})", lambda d, t=tab, p=path, f=fmt, sm=smooth_scroll: self._start_full_screenshot(t, d, p, f, sm))

    def _start_full_screenshot(self, tab, dims, path, fmt, smooth_scroll=True):
        if not dims or not tab or not tab.view:
            return
        width = max(1, min(int(dims.get("w", tab.view.width())), 30000))
        original_height = max(1, int(dims.get("h", tab.view.height())))
        height = min(original_height, 30000)
        if original_height > height:
            QMessageBox.information(
                self, "Full-page screenshot",
                "This page is longer than the 30,000 px safety limit. The screenshot will include only the first 30,000 px."
            )
        view = tab.view
        viewport_width = max(1, int(dims.get("vw", view.width())))
        viewport_height = max(1, int(dims.get("vh", view.height())))
        # Use instant movement for deterministic tile coordinates. The "auto-scroll"
        # mode means progressive capture with a lazy-load settling delay, not CSS
        # smooth animation (which can still be in flight when a tile is grabbed).
        behavior = "instant"
        prep = f"""(function(){{
          window.__neutronShotY=window.scrollY;
          window.__neutronShotX=window.scrollX;
          window.__neutronShotScrollBehavior=document.documentElement.style.scrollBehavior;
          document.documentElement.style.scrollBehavior='auto';
          window.__neutronShotStyles=[];
          document.querySelectorAll('*').forEach(e=>{{
            const p=getComputedStyle(e).position;
            if(p==='fixed'||p==='sticky'){{
              window.__neutronShotStyles.push([e,e.getAttribute('style')]);
              e.style.setProperty('visibility','hidden','important');
            }}
          }});
          window.scrollTo({{left:0,top:0,behavior:'{behavior}'}});
          return true;
        }})()"""
        self._screenshot_smooth_scroll = bool(smooth_scroll)
        wait_ms = 320 if smooth_scroll else 80
        view.page().runJavaScript(
            prep,
            lambda *_: QTimer.singleShot(
                wait_ms,
                lambda: self._capture_screenshot_tiles(tab, width, height, viewport_width, viewport_height, path, fmt, 0, 0, None)
            )
        )

    def _capture_screenshot_tiles(self, tab, width, height, viewport_width, viewport_height, path, fmt, x, y, canvas):
        try:
            if not tab or not tab.view:
                return
            view = tab.view
            shot = view.grab().toImage()
            if shot.isNull():
                self._finish_screenshot_restore(tab)
                QMessageBox.warning(self, APP_NAME, "Could not capture this page.")
                return
            scale = shot.width() / max(1, viewport_width)
            if canvas is None:
                out_w = max(1, int(width * scale))
                out_h = max(1, int(height * scale))
                if out_w * out_h > 90_000_000:
                    self._finish_screenshot_restore(tab)
                    QMessageBox.warning(
                        self, APP_NAME,
                        "The page is too large for a single screenshot (90 megapixel safety limit)."
                    )
                    return
                canvas = QImage(out_w, out_h, QImage.Format.Format_RGB32)
                if canvas.isNull():
                    self._finish_screenshot_restore(tab)
                    QMessageBox.warning(self, APP_NAME, "Not enough memory to create the full-page screenshot.")
                    return
                canvas.fill(QColor("white"))

            dest_x, dest_y = int(x * scale), int(y * scale)
            src_w = min(shot.width(), max(0, canvas.width() - dest_x))
            src_h = min(shot.height(), max(0, canvas.height() - dest_y))
            if src_w > 0 and src_h > 0:
                painter = QPainter(canvas)
                painter.drawImage(dest_x, dest_y, shot, 0, 0, src_w, src_h)
                painter.end()

            viewport_w = max(1, viewport_width)
            viewport_h = max(1, viewport_height)
            if x + viewport_w < width:
                next_x, next_y = x + viewport_w, y
            elif y + viewport_h < height:
                next_x, next_y = 0, y + viewport_h
            else:
                self._save_full_screenshot(tab, canvas, path, fmt)
                return

            behavior = "instant"
            wait_ms = 320 if getattr(self, "_screenshot_smooth_scroll", True) else 80

            def after_scroll(actual):
                if not tab or not tab.view:
                    return
                actual = actual if isinstance(actual, dict) else {}
                actual_x = max(0, int(actual.get("x", x)))
                actual_y = max(0, int(actual.get("y", y)))
                if actual_x == x and actual_y == y:
                    self._save_full_screenshot(tab, canvas, path, fmt)
                    return
                QTimer.singleShot(
                    wait_ms,
                    lambda: self._capture_screenshot_tiles(
                        tab, width, height, viewport_width, viewport_height, path, fmt, actual_x, actual_y, canvas
                    )
                )

            scroll_js = (
                f"window.scrollTo({{left:{next_x},top:{next_y},behavior:'{behavior}'}});true"
            )
            view.page().runJavaScript(
                scroll_js,
                lambda *_: QTimer.singleShot(
                    wait_ms,
                    lambda: view.page().runJavaScript(
                        "({x:window.scrollX,y:window.scrollY})", after_scroll
                    )
                )
            )
        except Exception as exc:
            log.exception("capture screenshot tile")
            self._finish_screenshot_restore(tab)
            try:
                QMessageBox.warning(self, APP_NAME, f"Screenshot failed: {exc}")
            except RuntimeError:
                pass

    def _save_full_screenshot(self, tab, canvas, path, fmt):
        try:
            ok = canvas.save(path, "JPG" if fmt == "JPG" else "PNG", getattr(self, "_screenshot_jpg_quality", 92) if fmt == "JPG" else -1)
            self._finish_screenshot_restore(tab)
            if not ok:
                QMessageBox.warning(self, APP_NAME, "Could not write screenshot file.")
            else:
                self.statusBar().showMessage("Full-page screenshot saved", 4000)
        except Exception as exc:
            self._finish_screenshot_restore(tab)
            log.exception("save screenshot")
            QMessageBox.warning(self, APP_NAME, f"Screenshot failed: {exc}")

    def _finish_screenshot_restore(self, tab):
        try:
            tab.view.page().runJavaScript(r'''(function(){if(window.__neutronShotStyles){window.__neutronShotStyles.forEach(([e,s])=>{if(s===null)e.removeAttribute('style');else e.setAttribute('style',s);});delete window.__neutronShotStyles;}if(window.__neutronShotScrollBehavior!==undefined){document.documentElement.style.scrollBehavior=window.__neutronShotScrollBehavior;delete window.__neutronShotScrollBehavior;}window.scrollTo({top:window.__neutronShotY||0,left:window.__neutronShotX||0,behavior:'instant'});delete window.__neutronShotY;delete window.__neutronShotX;})()''')
        except Exception: log.exception("restore screenshot page state")

    def reader_mode(self):
        tab = self.current_tab()
        if not tab: return
        js = r'''(function(){const c=document.querySelector('article,main,[role=main]')||document.body;return {title:document.title,text:(c.innerText||'').slice(0,1000000),url:location.href};})()'''
        tab.view.page().runJavaScript(js, lambda d: self._open_reader(d or {}))

    def open_ocr(self):
        """Open the OCR drop area in a separate tab."""
        tab = self.add_tab(QUrl("about:blank"))
        tab.view.setHtml(OCR_HTML, QUrl(OCR_BASE_URL))
        self.statusBar().showMessage("OCR workspace opened in a new tab", 2500)

    def open_background_remover(self):
        """Open the client-side AI Background Remover workspace in a new tab."""
        tab = self.add_tab(QUrl("about:blank"))
        tab.view.setHtml(BG_REMOVER_HTML, QUrl(BG_BASE_URL))
        self.statusBar().showMessage("Background Remover workspace opened in a new tab", 2500)

    def open_calculator(self):
        """Open a self-contained Standard calculator in a new tab."""
        tab = self.add_tab(QUrl("about:blank"))
        tab.view.setHtml(CALCULATOR_HTML, QUrl("https://neutron-calculator.local/"))
        self.statusBar().showMessage("Calculator opened in a new tab", 2000)

    def open_base64_decoder(self):
        """Open the Base64 text/file decoder in a new tab."""
        tab = self.add_tab(QUrl("about:blank"))
        tab.view.setHtml(BASE64_DECODER_HTML, QUrl("https://neutron-d64.local/"))
        self.statusBar().showMessage("Base64 Decoder opened in a new tab", 2000)

    def open_base64_encoder(self):
        """Open the Base64 file/text encoder in a new tab."""
        tab = self.add_tab(QUrl("about:blank"))
        tab.view.setHtml(BASE64_ENCODER_HTML, QUrl("https://neutron-e64.local/"))
        self.statusBar().showMessage("Base64 Encoder opened in a new tab", 2000)

    def open_music_player(self):
        """Open music_player.html in a new tab using the same self-contained mechanism as D64/E64."""
        webapp_dir = ensure_bundled_webapp_files()
        html_file = resource_path("music_player.html") or (webapp_dir / "music_player.html")
        try:
            html_content = html_file.read_text(encoding="utf-8") if html_file and html_file.is_file() else MUSIC_PLAYER_HTML
        except OSError:
            html_content = MUSIC_PLAYER_HTML
        tab = self.add_tab(QUrl("about:blank"))
        tab.view.setHtml(html_content, QUrl("https://neutron-music.local/music_player.html"))
        self.statusBar().showMessage("Music Player opened in a new tab", 2000)

    def open_game_hub(self):
        """Open game_hub.html in a new tab (with links to Duck Runner, Othello, Tic-Tac-Toe, and Stellar Raid)."""
        webapp_dir = ensure_bundled_webapp_files()
        html_file = resource_path("game_hub.html") or (webapp_dir / "game_hub.html")
        if html_file and html_file.is_file():
            tab = self.add_tab(QUrl.fromLocalFile(str(html_file.resolve())))
        else:
            tab = self.add_tab(QUrl("about:blank"))
            base_url = QUrl.fromLocalFile(str((webapp_dir / "game_hub.html").resolve()))
            tab.view.setHtml(GAME_HUB_HTML, base_url)
        self.statusBar().showMessage("Game Hub opened in a new tab", 2000)

    def open_media_diagnostics(self):
        """Open a self-contained media capability report for this QtWebEngine build."""
        tab = self.add_tab(QUrl("about:blank"))
        tab.view.setHtml(MEDIA_DIAGNOSTICS_HTML, QUrl("https://neutron-media.local/"))
        self.statusBar().showMessage("Video diagnostics opened in a new tab", 2000)

    def select_element_text(self, view, x, y):
        """Select and copy text belonging to the DOM element under the right-click point."""
        if not view or not view.page():
            return
        script = r'''(function(x,y){
          let el=document.elementFromPoint(x,y); if(!el)return '';
          if(el.matches && el.matches('input,textarea')){
            el.focus(); try{el.select()}catch(_){}; return String(el.value||'');
          }
          let target=el, text='';
          const getText=e=>String(e.innerText!==undefined?e.innerText:(e.textContent||''));
          for(let node=el,i=0;node&&i<8;node=node.parentElement,i++){
            const candidate=getText(node);
            if(candidate.trim()){target=node;text=candidate;break;}
          }
          const range=document.createRange(); range.selectNodeContents(target);
          const selection=window.getSelection(); selection.removeAllRanges(); selection.addRange(range);
          return text.trim().slice(0,5000000);
        })(%d,%d);''' % (int(x), int(y))
        def copied(text):
            if not isinstance(text, str) or not text:
                self.statusBar().showMessage("No text found in the clicked element", 2500)
                return
            QApplication.clipboard().setText(text)
            self.statusBar().showMessage(f"Selected element text and copied {len(text):,} characters", 3500)
        view.page().runJavaScript(script, copied)

    def _open_reader(self, data):
        title = html.escape(str(data.get("title", "Reader Mode")))
        url = html.escape(str(data.get("url", "")))
        paragraphs = "".join("<p>" + html.escape(line) + "</p>" for line in str(data.get("text", "")).splitlines() if line.strip())
        theme = str(self.cfg["reader_theme"])
        palette = {"dark": ("#17191f", "#eceff4", "#9aa3b5"), "sepia": ("#f4ecd8", "#463a2d", "#7d6d58"), "light": ("#ffffff", "#222222", "#667085")}
        bg, fg, muted = palette.get(theme, palette["light"])
        font_size = max(12, min(30, int(self.cfg["reader_font_size"])))
        page = f'''<!doctype html><html><head><meta charset="utf-8"><title>{title} - Reader</title><style>body{{max-width:820px;margin:40px auto;padding:0 24px;font:{font_size}px/1.8 Georgia,serif;background:{bg};color:{fg}}}h1{{font:700 34px/1.3 sans-serif}}.src{{font:12px sans-serif;color:{muted};margin-bottom:28px;overflow-wrap:anywhere}}p{{margin:0 0 1em}}</style></head><body><h1>{title}</h1><div class="src">{url}</div>{paragraphs}</body></html>'''
        t = self.add_tab(NEWTAB_URL)
        t.view.setHtml(page, QUrl(url) if url.startswith(("http://", "https://")) else QUrl())

    def show_permissions(self):
        def load(query):
            rows = []
            q = (query or "").lower()
            for origin, values in self.pd.permission_rules.items():
                for kind, allow in values.items():
                    cols = [origin, kind, "Always allow" if allow else "Always block"]
                    if not q or q in " ".join(cols).lower():
                        rows.append(((origin, kind), cols))
            return rows

        def forget(keys):
            for origin, kind in keys:
                if origin in self.pd.permission_rules:
                    self.pd.permission_rules[origin].pop(kind, None)
                    if not self.pd.permission_rules[origin]:
                        self.pd.permission_rules.pop(origin, None)
            if self.pd.permission_path:
                write_json(self.pd.permission_path, self.pd.permission_rules)
        self._show(ListDialog(self, "Website Permissions", ["Website", "Permission", "Decision"], load,
                              on_delete=forget, searchable=True, widths=(300, 180)))

    def set_tab_group(self):
        tab = self.current_tab()
        if not tab: return
        name, ok = QInputDialog.getText(self, "Tab Group", "Group name (blank removes group):", text=tab.group)
        if ok:
            tab.group = name.strip()[:32]
            self.on_title(tab, tab.view.title() or "New Tab")
            self._save_session_snapshot()

    def tab_context_menu(self, pos):
        index = self.tabbar.tabAt(pos)
        if index < 0: return
        self.tabbar.setCurrentIndex(index)
        tab = self.stack.widget(index)
        menu = QMenu(self)
        menu.addAction("New tab", lambda: self.add_tab(NEWTAB_URL))
        menu.addAction("Set / change group...", self.set_tab_group)
        menu.addAction("Remove from group", lambda: self._clear_tab_group(tab))
        menu.addSeparator()
        menu.addAction("Duplicate tab", lambda: self.add_tab(QUrl(tab.view.url())))
        menu.addAction("Unpin tab" if tab.pinned else "Pin tab", lambda: self.toggle_pin_tab(tab))
        menu.addAction("Unmute tab" if tab.muted else "Mute tab", lambda: self.toggle_mute_tab(tab))
        menu.addAction("Suspend this tab", lambda: self._set_tab_lifecycle(tab, "Frozen"))
        menu.addAction("Close tab", lambda: self.close_tab_obj(tab))
        menu.exec(self.tabbar.mapToGlobal(pos)); menu.deleteLater()

    def _clear_tab_group(self, tab):
        tab.group = ""
        self.on_title(tab, tab.view.title() or "New Tab")
        self._save_session_snapshot()

    def toggle_pin_tab(self, tab=None):
        tab = tab or self.current_tab()
        if not tab:
            return
        tab.pinned = not bool(tab.pinned)
        current_index = self.tab_index(tab)
        if current_index >= 0:
            if tab.pinned:
                # Keep pinned tabs together at the leading edge of the tab strip.
                target = sum(
                    1 for i in range(self.stack.count())
                    if i != current_index and isinstance(self.stack.widget(i), BrowserTab)
                    and self.stack.widget(i).pinned and i < current_index
                )
            else:
                target = sum(
                    1 for i in range(self.stack.count())
                    if i != current_index and isinstance(self.stack.widget(i), BrowserTab)
                    and self.stack.widget(i).pinned
                )
            target = max(0, min(target, self.tabbar.count() - 1))
            if target != current_index:
                self.tabbar.moveTab(current_index, target)
        self.on_title(tab, tab.view.title() or "New Tab")
        self._save_session_snapshot()
        self.statusBar().showMessage("Tab pinned" if tab.pinned else "Tab unpinned", 2500)

    def toggle_mute_tab(self, tab=None):
        tab = tab or self.current_tab()
        if not tab:
            return
        tab.muted = not bool(tab.muted)
        try:
            tab.view.page().setAudioMuted(tab.muted)
        except (AttributeError, RuntimeError):
            tab.muted = False
            QMessageBox.information(self, APP_NAME, "Audio mute is not supported by this Qt WebEngine build.")
            return
        self.on_title(tab, tab.view.title() or "New Tab")
        self._save_session_snapshot()
        self.statusBar().showMessage("Tab muted" if tab.muted else "Tab unmuted", 2500)

    def _vault_auto_lock_check(self):
        vault = self.pd.vault
        if vault and vault.unlocked() and vault._last_access and time.time() - vault._last_access >= 600:
            vault.lock()
            self.statusBar().showMessage("Password Vault auto-locked after 10 minutes of inactivity", 5000)

    def _auto_suspend_check(self):
        minutes = int(self.cfg["auto_suspend_minutes"] or 0)
        if minutes <= 0:
            return
        now = time.time()
        for i in range(self.stack.count()):
            tab = self.stack.widget(i)
            if isinstance(tab, BrowserTab) and tab is not self.current_tab() and not tab.loading:
                if now - getattr(tab, "last_activated", now) >= minutes * 60 and not tab.suspended:
                    self._set_tab_lifecycle(tab, "Frozen")

    def set_auto_suspend(self):
        choices = ["Off", "5", "10", "15", "30", "60"]
        current = str(self.cfg["auto_suspend_minutes"] or "Off")
        selected, ok = QInputDialog.getItem(self, "Automatic Tab Suspend", "Suspend inactive tabs after (minutes):", choices, max(0, choices.index(current) if current in choices else 0), False)
        if ok:
            self.cfg["auto_suspend_minutes"] = 0 if selected == "Off" else int(selected)
            self.cfg.save()

    def _set_tab_lifecycle(self, tab, state):
        try:
            lifecycle = getattr(QWebEnginePage, "LifecycleState", None)
            target = getattr(lifecycle, state, None) if lifecycle else None
            setter = getattr(tab.view.page(), "setLifecycleState", None)
            if target is None or not callable(setter):
                if state == "Frozen":
                    self.statusBar().showMessage("Tab freezing requires a Qt WebEngine build with page lifecycle support.", 5000)
                return False
            setter(target)
            tab.suspended = state == "Frozen"
            return True
        except Exception:
            log.exception("tab lifecycle")
            return False

    def suspend_inactive_tabs(self):
        count = 0
        for i in range(self.stack.count()):
            tab = self.stack.widget(i)
            if isinstance(tab, BrowserTab) and tab is not self.current_tab() and self._set_tab_lifecycle(tab, "Frozen"):
                count += 1
        self.statusBar().showMessage(f"Suspended {count} inactive tab(s)", 3500)

    def show_passwords(self):
        v = self.pd.vault
        if not unlock_vault_ui(self, v):
            return

        def reveal(ks):
            for i, o, u, p in v.all():
                if i in ks:
                    QMessageBox.information(self, o, f"Username: {u}\nPassword: {p}")

        def backup(_):
            path, _ = QFileDialog.getSaveFileName(self, "Export encrypted vault backup", "Neutron_Vault_Backup.nvbackup", "Neutron encrypted backup (*.nvbackup)")
            if path:
                try: v.backup(Path(path)); QMessageBox.information(self, APP_NAME, "Encrypted vault backup saved.")
                except Exception as exc: QMessageBox.warning(self, APP_NAME, str(exc))
        def restore(_):
            path, _ = QFileDialog.getOpenFileName(self, "Import encrypted vault backup", "", "Neutron encrypted backup (*.nvbackup)")
            if path and QMessageBox.question(self, APP_NAME, "Replace this profile's current Password Vault with the selected backup?") == QMessageBox.StandardButton.Yes:
                try:
                    v.restore_backup(Path(path)); QMessageBox.information(self, APP_NAME, "Backup imported. Unlock it with the backup's master password.")
                except Exception as exc: QMessageBox.warning(self, APP_NAME, str(exc))
        def change_master(_):
            entries = [{"origin": o, "item": {"u": u, "p": pw}} for _, o, u, pw in v.all()]
            new_pw = prompt_master_password(
                self, "Change Master Password",
                "Choose a new master password. All saved entries will be re-encrypted.",
            )
            if new_pw is None:
                return
            try:
                v._write_scrypt_vault(new_pw, entries)
                QMessageBox.information(self, APP_NAME, "Master password changed. All entries were re-encrypted.")
            except Exception as exc:
                log.exception("change master password")
                QMessageBox.critical(self, APP_NAME, f"Could not change master password: {exc}")
        def lock_now(_):
            v.lock()
            QMessageBox.information(self, APP_NAME, "Password Vault locked.")
        self._show(ListDialog(self, "Saved passwords", ["Site", "Username", "Password"],
                              lambda q: [(i, [o, u, "••••••••"]) for i, o, u, p in v.all() if q.lower() in (o + u).lower()],
                              on_delete=v.delete, searchable=True, extras=[("Reveal", reveal), ("Change master password", change_master), ("Lock vault now", lock_now), ("Export encrypted backup", backup), ("Import backup", restore)], widths=(320, 200)))

    def show_extensions(self):
        em = self.pd.extensions
        if self.pd.incognito:
            QMessageBox.information(self, APP_NAME, "Extensions are not available in Incognito mode.")
            return
        if not em.supported:
            QMessageBox.warning(self, "Extensions", f"This Qt build has no extension support.\nQt {QT_VERSION_STR} / PyQt {PYQT_VERSION_STR}.\n"
                                "Needs Qt/PyQt 6.10+ (pip install -U PyQt6 PyQt6-WebEngine).\n\n"
                                "Fallback: put .js files in Profiles/<name>/UserScripts/ (userscripts).")

        def add_dir(_):
            d = QFileDialog.getExistingDirectory(self, "Select unpacked extension folder")
            if d:
                em.add_dir(d)

        def add_file(_):
            p, _ = QFileDialog.getOpenFileName(self, "Select extension package", "", "Extension (*.crx *.zip)")
            if p:
                em.add_file(p)

        def popup(ks):
            u = em.popup_url(ks[0]) if ks else None
            if u:
                PopupWindow(self, self.pd.profile, u).show()
            else:
                QMessageBox.information(self, "Extensions", "This extension has no popup (or it is not loaded).")

        self._show(ListDialog(self, "Extensions (experimental)", ["Name", "Version", "Status"], lambda q: em.rows(),
                              on_delete=lambda ks: [em.remove(k) for k in ks],
                              extras=[("Add folder...", add_dir), ("Add CRX/ZIP...", add_file), ("Open popup", popup)], widths=(300, 80)))

    def show_settings(self):
        SettingsDialog(self).exec()

    def show_about(self):
        m = re.search(r"Chrome/([\d.]+)", self.pd.profile.httpUserAgent())
        QMessageBox.about(self, "About Neutron", f"<h3>{APP_NAME} {APP_VERSION}</h3>Portable web browser<br>"
                          f"Chromium {m.group(1) if m else '?'} - Qt {QT_VERSION_STR} - PyQt {PYQT_VERSION_STR}<br>"
                          f"Data folder: {DATA_DIR}")

    def clear_browsing_data(self):
        if QMessageBox.question(self, APP_NAME, "Clear history, cache and cookies for this profile?") != QMessageBox.StandardButton.Yes:
            return
        p = self.pd.profile
        p.clearHttpCache()
        p.cookieStore().deleteAllCookies()
        p.clearAllVisitedLinks()
        if self.pd.history:
            self.pd.history.clear()
        self.statusBar().showMessage("Browsing data cleared", 3000)

    # ---------- close ----------
    def closeEvent(self, e):
        try:
            last_of_profile = self.ctx.windows_of(self.pd) <= 1
            if not self.pd.incognito:
                if self._snap_timer.isActive():
                    self._snap_timer.stop()
                self._save_session_snapshot_now()
                self.cfg["last_profile"] = self.pd.name
                self.cfg["window_geometry"] = bytes(self.saveGeometry().toBase64()).decode()
                self.cfg.save()
                if last_of_profile:
                    tabs = []
                    for i in range(self.stack.count()):
                        w = self.stack.widget(i)
                        if isinstance(w, BrowserTab):
                            tabs.append({
                                "url": session_url(w.view.url()),
                                "group": w.group,
                                "pinned": bool(w.pinned),
                                "muted": bool(w.muted),
                            })
                    self.pd.save_session(tabs)
            for i in range(self.stack.count()):
                w = self.stack.widget(i)
                if isinstance(w, BrowserTab):
                    w.dispose()
        except Exception:
            log.exception("closeEvent")
        self.ctx.window_closed(self)
        e.accept()


# ============================================================
# 10) Application context
# ============================================================
class NeutronApp:
    def __init__(self, qt: QApplication, cfg: Config):
        self.qt, self.cfg = qt, cfg
        self.profiles: dict[str, ProfileData] = {}
        self.windows: list[BrowserWindow] = []
        self.incognito_pd: Optional[ProfileData] = None
        self.downloads = DownloadManager(cfg)
        self.image_workers = set()
        qt.aboutToQuit.connect(self.on_quit)

    def list_profiles(self):
        names = {d.name for d in PROFILES_DIR.iterdir() if d.is_dir()} | {"Default"}
        return sorted(names, key=str.lower)

    def get_profile(self, name: str) -> ProfileData:
        name = safe_name(name)
        if name not in self.profiles:
            self.profiles[name] = ProfileData(self, name)
        return self.profiles[name]

    def get_incognito(self) -> ProfileData:
        if self.incognito_pd is None:
            self.incognito_pd = ProfileData(self, "Incognito", incognito=True)
        return self.incognito_pd

    def open_profile_names(self):
        return {w.pd.name for w in self.windows if not w.pd.incognito}

    def windows_of(self, pd):
        return sum(1 for w in self.windows if w.pd is pd)

    def delete_profile(self, name):
        self.profiles.pop(name, None)
        shutil.rmtree(PROFILES_DIR / safe_name(name), ignore_errors=True)

    def open_window(self, pd: ProfileData, urls=None, blank=False) -> BrowserWindow:
        w = BrowserWindow(self, pd)
        self.windows.append(w)
        if not blank:
            items = list(urls or [NEWTAB_URL])
            # Restore pinned tabs first while retaining their relative order.
            items = sorted(
                enumerate(items),
                key=lambda pair: (not bool(pair[1].get("pinned", False)) if isinstance(pair[1], dict) else True, pair[0]),
            )
            for _, item in items:
                group, pinned, muted = "", False, False
                if isinstance(item, dict):
                    group = str(item.get("group", ""))[:32]
                    pinned = bool(item.get("pinned", False))
                    muted = bool(item.get("muted", False))
                    item = item.get("url", "neutron://newtab")
                url = item if isinstance(item, QUrl) else smart_url(str(item), self.cfg)
                tab = w.add_tab(None)
                tab.group, tab.pinned, tab.muted = group, pinned, muted
                if muted:
                    try:
                        tab.view.page().setAudioMuted(True)
                    except (AttributeError, RuntimeError):
                        tab.muted = False
                if group or pinned or muted:
                    w.on_title(tab, "New Tab")
                tab.view.load(url)
        w.show()
        w.activateWindow()
        return w

    def window_closed(self, w):
        if w in self.windows:
            self.windows.remove(w)
        pd = w.pd
        pd.windows -= 1
        if pd.incognito and pd.windows <= 0:
            self.incognito_pd = None
            QTimer.singleShot(1500, pd.deleteLater)  # ให้ page ถูกลบก่อน แล้วค่อยทิ้ง profile (ข้อมูลหายหมด)

    def apply_settings(self):
        self.qt.setStyleSheet("")
        for pd in list(self.profiles.values()) + ([self.incognito_pd] if self.incognito_pd else []):
            pd.apply_settings()
        for w in self.windows:
            w.apply_theme()
            w.bmbar.setVisible(bool(self.cfg["show_bookmarks_bar"]))
            w.a_bmbar.setChecked(bool(self.cfg["show_bookmarks_bar"]))

    def quit_all(self):
        for w in list(self.windows):
            w.close()

    def on_quit(self):
        try:
            self.cfg.save()
            if self.cfg["clear_on_exit"]:
                WIPE_MARKER.write_text("1")
        except OSError:
            log.exception("save configuration on quit")
        try:
            self.downloads.shutdown()
        except Exception:
            log.exception("download manager shutdown")
        # Cancel long-running Python workers before their QObject parents are destroyed.
        image_workers = list(self.image_workers)
        for worker in image_workers:
            try:
                worker.cancel()
            except Exception:
                log.exception("cancel image worker")
        for worker in image_workers:
            try:
                if worker.isRunning() and not worker.wait(8500):
                    log.error("Image worker did not stop within shutdown timeout")
            except Exception:
                log.exception("wait image worker")
        self.image_workers.clear()

        all_profiles = list(self.profiles.values()) + ([self.incognito_pd] if self.incognito_pd else [])
        for pd in all_profiles:
            if pd is None:
                continue
            try:
                pd.adblock.shutdown()
            except Exception:
                log.exception("stop AdBlock workers")
            try:
                if pd.vault:
                    pd.vault.lock()
            except Exception:
                log.exception("lock password vault")
            try:
                if pd.history:
                    pd.history.close()
            except Exception:
                log.exception("close history database")

    def start(self, args):
        incog = args.incognito
        pd = self.get_incognito() if incog else self.get_profile(args.profile or self.cfg["last_profile"])
        urls = list(args.urls)
        if not urls and not incog:
            mode = self.cfg["startup_mode"]
            if mode == "home":
                urls = [self.cfg["homepage"]]
            elif mode == "restore":
                urls = pd.load_session()
            elif mode == "custom":
                urls = [u.strip() for u in self.cfg["startup_urls"].splitlines() if u.strip()]
        self.open_window(pd, urls or None)


def process_wipe_marker():
    """ล้าง Storage/Cache ของทุกโปรไฟล์ถ้าครั้งก่อนเปิดตัวเลือก 'wipe on close' (ทำก่อนสร้าง profile)"""
    if WIPE_MARKER.exists():
        for d in PROFILES_DIR.iterdir():
            for sub in ("Storage", "Cache"):
                shutil.rmtree(d / sub, ignore_errors=True)
        try:
            WIPE_MARKER.unlink()
        except OSError:
            pass


_seen_errors: set = set()


def excepthook(t, v, tb):
    import traceback
    log.error("Unhandled: %s", "".join(traceback.format_exception(t, v, tb)))
    key = f"{t.__name__}:{v}"
    if key not in _seen_errors and QApplication.instance():
        _seen_errors.add(key)
        QMessageBox.critical(None, APP_NAME, f"Unexpected error:\n{t.__name__}: {v}\n\nSee UserData/neutron.log")


def install_watchdogs(qt):
    """Dump all Python stacks when the Qt event loop has not ticked for 6 seconds."""
    handle = (DATA_DIR / "hang.log").open("a", buffering=1, encoding="utf-8")
    try:
        faulthandler.enable(file=handle, all_threads=True)
    except Exception:
        log.exception("faulthandler enable")
    beat = {"time": time.monotonic()}
    timer = QTimer(qt)
    timer.setInterval(500)
    timer.timeout.connect(lambda: beat.__setitem__("time", time.monotonic()))
    timer.start()
    stop_event = threading.Event()

    def watch():
        last_dump = 0.0
        while not stop_event.wait(1.0):
            now = time.monotonic()
            stalled = now - beat["time"]
            if stalled > 6.0 and now - last_dump > 30.0:
                last_dump = now
                try:
                    handle.write(f"\n=== Qt UI stalled {stalled:.1f}s at {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n")
                    faulthandler.dump_traceback(file=handle, all_threads=True)
                except Exception:
                    log.exception("watchdog dump")

    thread = threading.Thread(target=watch, name="Neutron-Watchdog", daemon=True)
    thread.start()

    def stop_watchdog():
        stop_event.set()
        timer.stop()
        thread.join(timeout=1.5)
        try:
            faulthandler.disable()
            handle.flush()
            handle.close()
        except Exception:
            pass

    qt.aboutToQuit.connect(stop_watchdog)
    qt._neutron_watchdog_timer = timer
    qt._neutron_watchdog_thread = thread
    qt._neutron_watchdog_stop = stop_event
    qt._neutron_hang_log = handle
    return handle


def configure_chromium_runtime_flags():
    """Configure Chromium & Qt Quick to work reliably on both GPU and GPU-less / onboard VGA machines."""
    # Force software OpenGL & QtQuick software backend so machines without a dedicated GPU
    # or with basic onboard VGA drivers never render a blank white/black WebEngine view.
    os.environ.setdefault("QT_OPENGL", "software")
    os.environ.setdefault("QT_QUICK_BACKEND", "software")
    os.environ.setdefault("QT_ANGLE_PLATFORM", "warp")
    try:
        QApplication.setAttribute(Qt.ApplicationAttribute.AA_UseSoftwareOpenGL, True)
        QApplication.setAttribute(Qt.ApplicationAttribute.AA_ShareOpenGLContexts, True)
    except Exception:
        pass

    flags = os.environ.get("QTWEBENGINE_CHROMIUM_FLAGS", "").strip()
    compat_switches = (
        "--lang=th",
        "--enable-smooth-scrolling",
        "--disable-gpu",
        "--disable-gpu-compositing",
        "--disable-gpu-rasterization",
        "--disable-gpu-sandbox",
        "--disable-software-rasterizer",
        "--in-process-gpu",
        "--ignore-gpu-blocklist",
    )
    for switch in compat_switches:
        if switch.split("=", 1)[0] not in flags:
            flags = (flags + " " + switch).strip()

    if sys.platform == "win32":
        wanted = {"PlatformHEVCDecoderSupport"}
        match = re.search(r"--enable-features=(?:\"([^\"]*)\"|'([^']*)'|([^\s]+))", flags)
        if match:
            existing = next((g for g in match.groups() if g is not None), "")
            features = [x.strip() for x in existing.split(",") if x.strip()]
            wanted.update(features)
            replacement = "--enable-features=" + ",".join(sorted(wanted))
            flags = flags[:match.start()] + replacement + flags[match.end():]
        else:
            flags = (flags + " --enable-features=" + ",".join(sorted(wanted))).strip()

    os.environ["QTWEBENGINE_CHROMIUM_FLAGS"] = flags
    log.info("QTWEBENGINE_CHROMIUM_FLAGS=%s", flags)
    log.info("Software rendering fallback enabled for onboard VGA / GPU-less systems")


def log_media_runtime_versions():
    """Log the exact QtWebEngine/Chromium versions for support diagnostics."""
    try:
        from PyQt6 import QtWebEngineCore as core
        values = {}
        for name in ("qWebEngineVersion", "qWebEngineChromiumVersion", "qWebEngineChromiumSecurityPatchVersion"):
            fn = getattr(core, name, None)
            if callable(fn):
                try:
                    values[name] = fn()
                except Exception as exc:
                    values[name] = f"unavailable: {exc}"
        log.info("Media runtime versions: %s", json.dumps(values, ensure_ascii=False))
    except Exception:
        log.exception("Could not read QtWebEngine media versions")


def main():
    ap = argparse.ArgumentParser(add_help=False)
    ap.add_argument("urls", nargs="*")
    ap.add_argument("--profile")
    ap.add_argument("--incognito", action="store_true")
    args, qt_args = ap.parse_known_args()
    cfg = Config(CONFIG_FILE)

    configure_chromium_runtime_flags()

    scheme = QWebEngineUrlScheme(b"neutron")
    scheme.setSyntax(QWebEngineUrlScheme.Syntax.Host)
    flag = QWebEngineUrlScheme.Flag
    scheme_flags = flag.SecureScheme | flag.LocalAccessAllowed | flag.ServiceWorkersAllowed
    for optional in ("CorsEnabled", "DisplayIsPortAllowed"):
        value = getattr(flag, optional, None)
        if value is not None:
            scheme_flags |= value
    scheme.setFlags(scheme_flags)
    QWebEngineUrlScheme.registerScheme(scheme)

    qt = QApplication([sys.argv[0]] + qt_args)
    qt.setApplicationName(APP_NAME)
    qt.setApplicationVersion(APP_VERSION)
    qt.setStyle("Fusion")
    log_media_runtime_versions()
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("Neutron.Browser.1")
        except Exception:
            log.debug("Could not set Windows AppUserModelID", exc_info=True)
    qt.setWindowIcon(load_app_icon())
    ui_font = pick_font(["Leelawadee UI", "Segoe UI", "Noto Sans Thai", "Tahoma"])
    if ui_font:
        qt.setFont(QFont(ui_font, 10))
    sys.excepthook = excepthook
    qt._neutron_hang_log = install_watchdogs(qt)
    process_wipe_marker()
    ctx = NeutronApp(qt, cfg)
    try:
        ctx.start(args)
    except Exception:
        log.exception("startup failed")
        QMessageBox.critical(None, APP_NAME, "Failed to start. See UserData/neutron.log")
        return 1
    return qt.exec()


if __name__ == "__main__":
    sys.exit(main())