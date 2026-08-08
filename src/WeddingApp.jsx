import React, { useEffect, useMemo, useRef, useState } from "react";
import {
  Phone,
  Calendar,
  MapPin,
  Check,
  X,
  ArrowRight,
  Heart,
  Lock,
  Search,
  Plus,
  Pencil,
  Trash2,
  Camera,
  ScanLine,
  MessageSquare,
  LogIn,
  Users,
  AlertCircle,
  Download,
  Send,
  ExternalLink,
  XCircle,
  CheckCircle2,
  Loader2,
  Settings,
  Baby,
  CreditCard,
  Printer,
  PhoneOff,
  ShieldCheck,
} from "lucide-react";

const COLORS = {
  cream: "#F7F1E6",
  card: "#FBF8F1",
  olive: "#5C6B3E",
  oliveDark: "#47542F",
  gold: "#C9A227",
  mutedGold: "#D9CFA6",
  textDark: "#3A3428",
  mutedText: "#8B8270",
  error: "#B5514A",
  orange: "#D97706",
  orangeTint: "#FBEBD2",
};

const EVENT = {
  title: "حفل زواج عبدالله وميار",
  dateLabel: "31-08-2026",
  dateHijri: "1448.03.18",
  dayName: "الاثنين",
  venue: "قاعة الفخامة بلس - جدة",
  mapUrl: "https://maps.app.goo.gl/AopSxNrnvvJbYQLr8?g_st=aw",
  familyLine: "آل الإمام وآل أبو شال",
  coupleNames: "عبدالله & ميار",
};

const ADMIN_PASSWORD = "693193";
const SCAN_PASSWORD = "0000";

// Staff-only instruction shown at check-in scan — never surfaced to the guest-facing pass.
const PHONE_POLICIES = {
  confiscate: { label: "ينسحب منه الجوال", Icon: PhoneOff, color: COLORS.error },
  pouch: { label: "يوضع جراب على الجوال", Icon: ShieldCheck, color: COLORS.orange },
  allow: { label: "يسمح بدخول الجوال بدون تغطية", Icon: Phone, color: COLORS.olive },
};

/* =========================================================================
 * QR Code encoder — byte mode, EC level L, versions 1-5, plain-JS implementation.
 * Verified independently against jsQR across boundary and random payloads
 * before integration (no third-party QR image API is used anywhere).
 * ========================================================================= */
const GF_EXP = new Array(512);
const GF_LOG = new Array(256);
(function initGF() {
  let x = 1;
  for (let i = 0; i < 255; i++) {
    GF_EXP[i] = x;
    GF_LOG[x] = i;
    x <<= 1;
    if (x & 0x100) x ^= 0x11d;
  }
  for (let i = 255; i < 512; i++) GF_EXP[i] = GF_EXP[i - 255];
})();
function gfMul(a, b) {
  if (a === 0 || b === 0) return 0;
  return GF_EXP[GF_LOG[a] + GF_LOG[b]];
}
function rsGeneratorPoly(ecCount) {
  let gen = [1];
  for (let i = 0; i < ecCount; i++) {
    const next = new Array(gen.length + 1).fill(0);
    for (let j = 0; j < gen.length; j++) {
      next[j] ^= gen[j];
      next[j + 1] ^= gfMul(gen[j], GF_EXP[i]);
    }
    gen = next;
  }
  return gen;
}
function rsComputeECC(data, ecCount) {
  const gen = rsGeneratorPoly(ecCount);
  const result = data.slice().concat(new Array(ecCount).fill(0));
  for (let i = 0; i < data.length; i++) {
    const factor = result[i];
    if (factor !== 0) {
      for (let j = 0; j < gen.length; j++) {
        result[i + j] ^= gfMul(gen[j], factor);
      }
    }
  }
  return result.slice(data.length, data.length + ecCount);
}
const VERSION_INFO_L = {
  1: { data: 19, ec: 7 },
  2: { data: 34, ec: 10 },
  3: { data: 55, ec: 15 },
  4: { data: 80, ec: 20 },
  5: { data: 108, ec: 26 },
};
function sizeForVersion(v) {
  return 17 + 4 * v;
}
class BitBuffer {
  constructor() {
    this.bits = [];
  }
  push(val, len) {
    for (let i = len - 1; i >= 0; i--) this.bits.push((val >>> i) & 1);
  }
  get length() {
    return this.bits.length;
  }
}
function encodeData(text, version) {
  const info = VERSION_INFO_L[version];
  const capacityBits = info.data * 8;
  const bytes = [];
  for (let i = 0; i < text.length; i++) bytes.push(text.charCodeAt(i) & 0xff);
  const bb = new BitBuffer();
  bb.push(0b0100, 4);
  bb.push(bytes.length, 8);
  for (const b of bytes) bb.push(b, 8);
  const termLen = Math.min(4, capacityBits - bb.length);
  if (termLen > 0) bb.push(0, termLen);
  while (bb.length % 8 !== 0) bb.bits.push(0);
  const padBytes = [0xec, 0x11];
  let pi = 0;
  while (bb.length < capacityBits) {
    bb.push(padBytes[pi % 2], 8);
    pi++;
  }
  const dataCodewords = [];
  for (let i = 0; i < bb.bits.length; i += 8) {
    let byte = 0;
    for (let j = 0; j < 8; j++) byte = (byte << 1) | bb.bits[i + j];
    dataCodewords.push(byte);
  }
  return dataCodewords;
}
function chooseVersion(text) {
  for (let v = 1; v <= 5; v++) {
    const info = VERSION_INFO_L[v];
    const bitsNeeded = 4 + 8 + 8 * text.length;
    if (Math.ceil(bitsNeeded / 8) <= info.data) return v;
  }
  return 5;
}
function makeMatrix(size) {
  const m = [];
  for (let i = 0; i < size; i++) m.push(new Array(size).fill(false));
  return m;
}
function makeBoolMatrix(size, val) {
  const m = [];
  for (let i = 0; i < size; i++) m.push(new Array(size).fill(val));
  return m;
}
function placeFinderPattern(matrix, isFunc, row, col) {
  for (let dr = -1; dr <= 7; dr++) {
    for (let dc = -1; dc <= 7; dc++) {
      const r = row + dr,
        c = col + dc;
      if (r < 0 || r >= matrix.length || c < 0 || c >= matrix.length) continue;
      isFunc[r][c] = true;
      const inCore = dr >= 0 && dr <= 6 && dc >= 0 && dc <= 6;
      let dark = false;
      if (inCore) {
        const border = dr === 0 || dr === 6 || dc === 0 || dc === 6;
        const center = dr >= 2 && dr <= 4 && dc >= 2 && dc <= 4;
        dark = border || center;
      }
      matrix[r][c] = dark;
    }
  }
}
function placeTimingPatterns(matrix, isFunc, size) {
  for (let i = 8; i < size - 8; i++) {
    if (!isFunc[6][i]) {
      matrix[6][i] = i % 2 === 0;
      isFunc[6][i] = true;
    }
    if (!isFunc[i][6]) {
      matrix[i][6] = i % 2 === 0;
      isFunc[i][6] = true;
    }
  }
}
function placeAlignmentPattern(matrix, isFunc, size, version) {
  if (version === 1) return;
  const pos = size - 7;
  for (let dr = -2; dr <= 2; dr++) {
    for (let dc = -2; dc <= 2; dc++) {
      const r = pos + dr,
        c = pos + dc;
      const ring = Math.max(Math.abs(dr), Math.abs(dc));
      matrix[r][c] = ring !== 1;
      isFunc[r][c] = true;
    }
  }
}
function reserveFormatAreas(isFunc, size) {
  for (let i = 0; i <= 8; i++) {
    isFunc[8][i] = true;
    isFunc[i][8] = true;
  }
  for (let i = 0; i < 8; i++) {
    isFunc[8][size - 1 - i] = true;
    isFunc[size - 1 - i][8] = true;
  }
}
function placeDarkModule(matrix, isFunc, version) {
  const r = 4 * version + 9;
  matrix[r][8] = true;
  isFunc[r][8] = true;
}
function placeData(matrix, isFunc, size, codewords) {
  const totalBits = codewords.length * 8;
  let bitIdx = 0;
  let upward = true;
  for (let right = size - 1; right >= 1; right -= 2) {
    if (right === 6) right = 5;
    for (let vert = 0; vert < size; vert++) {
      for (let j = 0; j < 2; j++) {
        const x = right - j;
        const y = upward ? size - 1 - vert : vert;
        if (!isFunc[y][x]) {
          let bit = false;
          if (bitIdx < totalBits) {
            const byte = codewords[bitIdx >>> 3];
            bit = ((byte >>> (7 - (bitIdx & 7))) & 1) !== 0;
          }
          matrix[y][x] = bit;
          bitIdx++;
        }
      }
    }
    upward = !upward;
  }
}
function applyMask(matrix, isFunc, size, maskFn) {
  const out = makeMatrix(size);
  for (let r = 0; r < size; r++) {
    for (let c = 0; c < size; c++) {
      let v = matrix[r][c];
      if (!isFunc[r][c] && maskFn(r, c)) v = !v;
      out[r][c] = v;
    }
  }
  return out;
}
const MASK_FUNCS = [
  (r, c) => (r + c) % 2 === 0,
  (r, c) => r % 2 === 0,
  (r, c) => c % 3 === 0,
  (r, c) => (r + c) % 3 === 0,
  (r, c) => (Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0,
  (r, c) => ((r * c) % 2) + ((r * c) % 3) === 0,
  (r, c) => (((r * c) % 2) + ((r * c) % 3)) % 2 === 0,
  (r, c) => (((r + c) % 2) + ((r * c) % 3)) % 2 === 0,
];
function computePenalty(matrix, size) {
  let penalty = 0;
  for (let r = 0; r < size; r++) {
    let run = 1;
    for (let c = 1; c < size; c++) {
      if (matrix[r][c] === matrix[r][c - 1]) run++;
      else {
        if (run >= 5) penalty += 3 + (run - 5);
        run = 1;
      }
    }
    if (run >= 5) penalty += 3 + (run - 5);
  }
  for (let c = 0; c < size; c++) {
    let run = 1;
    for (let r = 1; r < size; r++) {
      if (matrix[r][c] === matrix[r - 1][c]) run++;
      else {
        if (run >= 5) penalty += 3 + (run - 5);
        run = 1;
      }
    }
    if (run >= 5) penalty += 3 + (run - 5);
  }
  for (let r = 0; r < size - 1; r++) {
    for (let c = 0; c < size - 1; c++) {
      const v = matrix[r][c];
      if (v === matrix[r][c + 1] && v === matrix[r + 1][c] && v === matrix[r + 1][c + 1]) penalty += 3;
    }
  }
  const pattern = [true, false, true, true, true, false, true];
  function matchesAt(getBit, i) {
    for (let k = 0; k < 7; k++) if (getBit(i + k) !== pattern[k]) return false;
    return true;
  }
  for (let r = 0; r < size; r++) {
    for (let c = 0; c <= size - 11; c++) {
      const getBit = (i) => matrix[r][i];
      if (matchesAt(getBit, c)) {
        const beforeOk = c >= 4 && [0, 1, 2, 3].every((k) => matrix[r][c - 1 - k] === false);
        const afterIdx = c + 7;
        const afterOk = afterIdx + 3 < size && [0, 1, 2, 3].every((k) => matrix[r][afterIdx + k] === false);
        if (beforeOk || afterOk) penalty += 40;
      }
    }
  }
  for (let c = 0; c < size; c++) {
    for (let r = 0; r <= size - 11; r++) {
      const getBit = (i) => matrix[i][c];
      if (matchesAt(getBit, r)) {
        const beforeOk = r >= 4 && [0, 1, 2, 3].every((k) => matrix[r - 1 - k][c] === false);
        const afterIdx = r + 7;
        const afterOk = afterIdx + 3 < size && [0, 1, 2, 3].every((k) => matrix[afterIdx + k][c] === false);
        if (beforeOk || afterOk) penalty += 40;
      }
    }
  }
  let dark = 0;
  for (let r = 0; r < size; r++) for (let c = 0; c < size; c++) if (matrix[r][c]) dark++;
  const percent = (dark * 100) / (size * size);
  const prevMultiple = Math.floor(Math.abs(percent - 50) / 5) * 5;
  penalty += (prevMultiple / 5) * 10;
  return penalty;
}
const FORMAT_GEN = 0x537;
function computeFormatBits(maskIndex) {
  const data = (0b01 << 3) | maskIndex;
  let d = data << 10;
  for (let i = 14; i >= 10; i--) {
    if ((d >>> i) & 1) d ^= FORMAT_GEN << (i - 10);
  }
  const bits = (data << 10) | d;
  return bits ^ 0x5412;
}
function placeFormatInfo(matrix, size, maskIndex) {
  const bits = computeFormatBits(maskIndex);
  for (let i = 0; i < 15; i++) {
    const mod = ((bits >>> i) & 1) !== 0;
    if (i < 6) matrix[i][8] = mod;
    else if (i < 8) matrix[i + 1][8] = mod;
    else matrix[size - 15 + i][8] = mod;
    if (i < 8) matrix[8][size - i - 1] = mod;
    else if (i < 9) matrix[8][15 - i - 1 + 1] = mod;
    else matrix[8][15 - i - 1] = mod;
  }
  matrix[size - 8][8] = true;
}
function encodeQR(text) {
  const version = chooseVersion(text);
  const size = sizeForVersion(version);
  const dataCodewords = encodeData(text, version);
  const ecCount = VERSION_INFO_L[version].ec;
  const ecCodewords = rsComputeECC(dataCodewords, ecCount);
  const allCodewords = dataCodewords.concat(ecCodewords);
  const matrix = makeMatrix(size);
  const isFunc = makeBoolMatrix(size, false);
  placeFinderPattern(matrix, isFunc, 0, 0);
  placeFinderPattern(matrix, isFunc, 0, size - 7);
  placeFinderPattern(matrix, isFunc, size - 7, 0);
  placeTimingPatterns(matrix, isFunc, size);
  placeAlignmentPattern(matrix, isFunc, size, version);
  reserveFormatAreas(isFunc, size);
  placeDarkModule(matrix, isFunc, version);
  placeData(matrix, isFunc, size, allCodewords);
  let bestPenalty = Infinity;
  let bestMatrix = null;
  for (let m = 0; m < 8; m++) {
    const masked = applyMask(matrix, isFunc, size, MASK_FUNCS[m]);
    placeFormatInfo(masked, size, m);
    const p = computePenalty(masked, size);
    if (p < bestPenalty) {
      bestPenalty = p;
      bestMatrix = masked;
    }
  }
  return { size, matrix: bestMatrix };
}

/* ========================================================================= */

function normalizeSaudiPhone(input) {
  let digits = String(input || "").replace(/\D/g, "");
  if (digits.startsWith("00966")) digits = digits.slice(5);
  else if (digits.startsWith("966")) digits = digits.slice(3);
  if (digits.startsWith("5") && digits.length === 9) digits = "0" + digits;
  return digits;
}
function isValidSaudiPhone(input) {
  return /^05\d{8}$/.test(normalizeSaudiPhone(input));
}
function formatDisplayPhone(phone) {
  const n = normalizeSaudiPhone(phone);
  return n || phone;
}
function todayLabel() {
  const d = new Date();
  return d.toISOString().slice(0, 10);
}

// Avoids visually-ambiguous characters (0/O, 1/I/L) so a hand-copied code stays unambiguous.
const PASS_CODE_CHARS = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
const usedPassCodes = new Set();
function generatePassCode() {
  let code;
  do {
    let raw = "";
    for (let i = 0; i < 8; i++) raw += PASS_CODE_CHARS[Math.floor(Math.random() * PASS_CODE_CHARS.length)];
    code = raw.slice(0, 4) + "-" + raw.slice(4);
  } while (usedPassCodes.has(code));
  usedPassCodes.add(code);
  return code;
}
function normalizePassCode(raw) {
  return String(raw || "")
    .toUpperCase()
    .replace(/[^A-Z0-9]/g, "");
}

const initialGuests = [
  { id: 101, name: "زهراء البنا", phone: "0504327254", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 102, name: "إيلاف إمام", phone: "0500078167", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 103, name: "أنفال إمام", phone: "0504648605", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 104, name: "آلاء إمام", phone: "0548775913", companions: 3, children: 1, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 105, name: "أبرار إمام", phone: "0504333951", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 106, name: "أفنان إمام", phone: "0553388987", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 107, name: "إسراء إمام", phone: "0504332525", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 108, name: "مدى كتبي زوجة أحمد إمام", phone: "0558865366", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 109, name: "إيناس زوجة عبدالله إمام", phone: "0562105944", companions: 2, children: 1, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 110, name: "نهى البنا زوجة محمد إمام", phone: "0598380366", companions: 3, children: 2, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 111, name: "ليان إمام", phone: "0555393864", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 112, name: "وئام المحروقي", phone: "0555062918", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 113, name: "رهام الصبحي زوجة عبيدة", phone: "0552375066", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 114, name: "رهام إمام", phone: "0598776822", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 115, name: "أسماء البنا", phone: "0556870483", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 116, name: "عصماء البنا", phone: "0503601497", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 117, name: "إيمان إبراهيم البنا", phone: "0545626420", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 118, name: "منى البنا", phone: "0503004612", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 119, name: "هند إبراهيم البنا", phone: "0506654606", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 120, name: "نجود زوجة خالد البنا", phone: "0546602200", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 121, name: "منال باناجة", phone: "0504339066", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 122, name: "مريم باناجة", phone: "0504162765", companions: 2, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 123, name: "نهى زوجة موسى باناجة", phone: "0567777616", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 124, name: "هند بوقري", phone: "0553283881", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 125, name: "آلاء زوجة عمر با ناجة", phone: "0555411751", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 126, name: "أسماء زوجة أنس البنا", phone: "0540934608", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 127, name: "لينة زوجة أيمن باناجة", phone: "0564851213", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 128, name: "رغد زوجة عبدالله شاهين", phone: "0541669323", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 129, name: "زهرة زوجة عبدالرجمن بوقري", phone: "0507675159", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 130, name: "سارة البنا", phone: "0566102951", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 131, name: "سعيدة زوجة بكر", phone: "0566199155", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 132, name: "عائشة البنا", phone: "0555663230", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 133, name: "فاطمة رشيد", phone: "0548490101", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 134, name: "غادة البنا", phone: "0501240445", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 135, name: "نهلة البنا", phone: "0598560470", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 136, name: "هناء سنبل", phone: "0556644432", companions: 0, children: 1, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 137, name: "ياسمين زوجة يوسف البنا", phone: "0590125902", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 138, name: "أفنان زوجة مصطفى شاهين", phone: "0536734172", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 139, name: "مليكة زوجة عبادة", phone: "0563947692", companions: 2, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 140, name: "أمل موصلي", phone: "0504623066", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 141, name: "أمامة المحروقي", phone: "0506682666", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 142, name: "خولة المحروقي", phone: "0597262676", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 143, name: "سمية المحروقي", phone: "0535414999", companions: 1, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 144, name: "فاطمة المحروقي", phone: "0594995678", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 145, name: "مريم المحروقي", phone: "0564002001", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 146, name: "هناء زوجة أسامة المحروقي", phone: "0536448820", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 147, name: "سيزن زوجة عبدالله المحروقي", phone: "0591376963", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 148, name: "حسنية مقري", phone: "0503685068", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 149, name: "خالة دولت", phone: "0504647550", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 150, name: "شروق آقو", phone: "0557505450", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 151, name: "شعاع آقو", phone: "0555678278", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 152, name: "شذى آقو", phone: "0554647550", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 153, name: "شيماء آقو", phone: "0504647552", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 154, name: "حنان عبيد", phone: "0504791873", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 155, name: "د.نسمة منصوري", phone: "0505683313", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 156, name: "فاطمة أبو العز", phone: "0508517104", companions: 3, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 157, name: "خالة انتظار خياط", phone: "0504627335", companions: 3, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 158, name: "سلوى جمجوم", phone: "0505625282", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 159, name: "دينا بارجاش", phone: "0561176221", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 160, name: "نجلاء البنا", phone: "0554344711", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 161, name: "لينة عبدالجواد", phone: "0501555088", companions: 2, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 162, name: "رغدة عبدالجواد", phone: "0504373145", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 163, name: "طنط رقية", phone: "0598820020", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 164, name: "ندى اسماعيل البنا", phone: "0556451118", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 165, name: "سارا اسماعيل البنا", phone: "0556451118", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 166, name: "عمة فاطمة", phone: "0555640776", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 167, name: "غدير عقيل", phone: "0594299255", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 168, name: "نادية عقيل", phone: "0555659024", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 169, name: "رودين عقيل", phone: "0548556477", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 170, name: "عمة نزيهة", phone: "0503621797", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 171, name: "ندى بدر الدين", phone: "0554636350", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 172, name: "امل بدر الدين", phone: "0505600072", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  { id: 173, name: "نهى غمري", phone: "0504386923", companions: 0, children: 0, status: "pending", checkedIn: false, passCode: generatePassCode(), phonePolicy: "pouch" },
  ...Array.from({ length: 100 }, (_, i) => ({
    id: 9001 + i,
    name: "",
    phone: "",
    passCode: generatePassCode(),
    companions: 0,
    children: 0,
    status: "confirmed",
    checkedIn: false,
    isExtraCard: true,
    issued: false,
    phonePolicy: "pouch",
  })),
];

const initialMessages = [];

/* ---------- small shared UI pieces ---------- */

function Ornament({ flipped = false, className = "" }) {
  return (
    <svg
      viewBox="0 0 200 20"
      className={`w-full h-4 ${className}`}
      style={{ transform: flipped ? "rotate(180deg)" : undefined }}
    >
      <line x1="0" y1="10" x2="70" y2="10" stroke={COLORS.gold} strokeWidth="1" opacity="0.6" />
      <line x1="130" y1="10" x2="200" y2="10" stroke={COLORS.gold} strokeWidth="1" opacity="0.6" />
      <circle cx="85" cy="10" r="2.5" fill={COLORS.gold} />
      <circle cx="100" cy="10" r="3.5" fill={COLORS.gold} />
      <circle cx="115" cy="10" r="2.5" fill={COLORS.gold} />
      <path d="M 78 10 Q 90 2 100 10 Q 110 18 122 10" stroke={COLORS.gold} strokeWidth="1" fill="none" opacity="0.5" />
    </svg>
  );
}

function IconCircle({ children, tone = "olive", size = 72 }) {
  const bg =
    tone === "olive" ? COLORS.olive : tone === "error" ? COLORS.error : tone === "gold" ? COLORS.gold : COLORS.mutedGold;
  return (
    <div
      className="rounded-full flex items-center justify-center shrink-0"
      style={{ width: size, height: size, backgroundColor: bg }}
    >
      {children}
    </div>
  );
}

function PrimaryButton({ children, onClick, disabled, className = "", type = "button" }) {
  return (
    <button
      type={type}
      onClick={onClick}
      disabled={disabled}
      className={`w-full rounded-2xl py-3.5 font-bold text-base transition active:scale-[0.98] disabled:opacity-50 disabled:active:scale-100 ${className}`}
      style={{ backgroundColor: disabled ? COLORS.mutedGold : COLORS.olive, color: disabled ? COLORS.mutedText : "#FFFFFF" }}
    >
      {children}
    </button>
  );
}

function SecondaryButton({ children, onClick, className = "", as = "button", href, target }) {
  const cls = `w-full rounded-2xl py-3.5 font-bold text-base border-2 transition active:scale-[0.98] flex items-center justify-center gap-2 ${className}`;
  const style = { borderColor: COLORS.olive, color: COLORS.olive, backgroundColor: "transparent" };
  if (as === "a") {
    return (
      <a href={href} target={target} rel="noreferrer" className={cls} style={style}>
        {children}
      </a>
    );
  }
  return (
    <button type="button" onClick={onClick} className={cls} style={style}>
      {children}
    </button>
  );
}

function Modal({ children, onClose, wide = false }) {
  return (
    <div className="fixed inset-0 z-50 flex items-end sm:items-center justify-center bg-black/50 p-0 sm:p-4" onClick={onClose}>
      <div
        onClick={(e) => e.stopPropagation()}
        className={`w-full ${wide ? "sm:max-w-lg" : "sm:max-w-md"} rounded-t-3xl sm:rounded-3xl p-6 max-h-[92vh] overflow-y-auto`}
        style={{ backgroundColor: COLORS.card }}
      >
        {children}
      </div>
    </div>
  );
}

function CornerControls({ onAdmin, onScan }) {
  return (
    <div className="fixed bottom-4 left-4 z-40 flex flex-col items-start gap-2">
      <button
        onClick={onAdmin}
        className="flex items-center gap-1.5 rounded-full px-3.5 py-2 text-xs font-bold shadow-lg active:scale-95 transition"
        style={{ backgroundColor: COLORS.oliveDark, color: COLORS.cream }}
      >
        <Settings size={14} />
        لوحة التحكم
      </button>
      <button
        onClick={onScan}
        className="flex items-center gap-1.5 rounded-full px-3.5 py-2 text-xs font-bold shadow-lg active:scale-95 transition"
        style={{ backgroundColor: COLORS.olive, color: "#fff" }}
      >
        <ScanLine size={14} />
        مسح الباركود
      </button>
    </div>
  );
}

function StatusPill({ status }) {
  const map = {
    pending: { label: "بانتظار الرد", bg: COLORS.mutedGold, text: COLORS.textDark },
    confirmed: { label: "مؤكد", bg: COLORS.olive, text: "#fff" },
    declined: { label: "معتذر", bg: COLORS.error, text: "#fff" },
  };
  const s = map[status] || map.pending;
  return (
    <span className="inline-block rounded-full px-2.5 py-1 text-xs font-bold" style={{ backgroundColor: s.bg, color: s.text }}>
      {s.label}
    </span>
  );
}

function PhonePolicyCallout({ value }) {
  const p = PHONE_POLICIES[value];
  if (!p) return null;
  const { Icon } = p;
  return (
    <div
      className="rounded-2xl p-4 flex items-center gap-3 mb-4"
      style={{ backgroundColor: `${p.color}1A`, border: `1.5px solid ${p.color}` }}
    >
      <div className="rounded-full flex items-center justify-center shrink-0" style={{ width: 44, height: 44, backgroundColor: p.color }}>
        <Icon size={22} color="#fff" />
      </div>
      <div>
        <p className="text-[11px] font-bold" style={{ color: p.color }}>
          إجراء الجوال عند الدخول
        </p>
        <p className="font-bold" style={{ color: COLORS.textDark }}>
          {p.label}
        </p>
      </div>
    </div>
  );
}

function PhonePolicyPill({ value }) {
  const p = PHONE_POLICIES[value];
  if (!p) {
    return (
      <span className="text-xs" style={{ color: COLORS.mutedText }}>
        —
      </span>
    );
  }
  const { Icon } = p;
  return (
    <span
      className="inline-flex items-center gap-1 rounded-full px-2.5 py-1 text-xs font-bold whitespace-nowrap"
      style={{ backgroundColor: `${p.color}1A`, color: p.color, border: `1px solid ${p.color}` }}
    >
      <Icon size={12} />
      {p.label}
    </span>
  );
}

/* ---------- screens ---------- */

function LandingScreen({ onConfirm }) {
  const hijriParts = EVENT.dateHijri.split(".");
  const hijriDMY = `${hijriParts[2]}-${hijriParts[1]}-${hijriParts[0]}`;

  return (
    <div className="min-h-screen flex flex-col justify-center px-5 py-10" style={{ backgroundColor: COLORS.cream }}>
      <div className="max-w-md mx-auto w-full">
        <div
          className="relative px-7 pt-12 pb-10 shadow-xl"
          style={{
            background: `linear-gradient(160deg, ${COLORS.olive}, ${COLORS.oliveDark})`,
            borderRadius: "140px 140px 18px 18px",
          }}
        >
          <div
            className="absolute inset-3 pointer-events-none"
            style={{ border: `1px solid ${COLORS.gold}`, borderRadius: "128px 128px 10px 10px", opacity: 0.5 }}
          />
          <div className="text-center relative">
            <p className="font-amiri text-2xl font-bold" style={{ color: COLORS.cream }}>
              أفراح
            </p>
            <p className="mt-1 text-sm leading-7" style={{ color: COLORS.cream }}>
              {EVENT.familyLine}
            </p>
            <div className="my-5 px-6">
              <Ornament />
            </div>
            <p className="text-sm" style={{ color: COLORS.cream }}>
              حفل زفاف
            </p>
            <h1 className="font-amiri text-4xl font-bold mt-1" style={{ color: COLORS.gold }}>
              {EVENT.coupleNames}
            </h1>
            <p className="mt-4 text-sm leading-7" style={{ color: COLORS.mutedGold }}>
              اللباس الساتر زينة ليلتنا / جنة الأطفال منازلهم
            </p>
            <div className="mt-6 space-y-1.5 text-sm">
              <p style={{ color: COLORS.cream }}>
                {EVENT.dayName} {EVENT.dateLabel}م · {hijriDMY}هـ
              </p>
              <p style={{ color: COLORS.cream }}>{EVENT.venue}</p>
            </div>
            <div className="mt-6 px-6">
              <Ornament flipped />
            </div>
          </div>
        </div>

        <div className="mt-6 space-y-3">
          <PrimaryButton onClick={onConfirm}>تأكيد الحضور</PrimaryButton>
          <SecondaryButton as="a" href={EVENT.mapUrl} target="_blank">
            <MapPin size={18} />
            لوكيشن القاعة
          </SecondaryButton>
        </div>
      </div>
    </div>
  );
}

function PhoneScreen({ onBack, onFound, onNotFound, guests }) {
  const [value, setValue] = useState("");
  const [touched, setTouched] = useState(false);
  const valid = isValidSaudiPhone(value);

  function submit() {
    setTouched(true);
    if (!isValidSaudiPhone(value)) return;
    const normalized = normalizeSaudiPhone(value);
    const guest = guests.find((g) => normalizeSaudiPhone(g.phone) === normalized);
    if (guest) onFound(guest);
    else onNotFound();
  }

  return (
    <div className="min-h-screen flex flex-col px-5 py-8" style={{ backgroundColor: COLORS.cream }}>
      <div className="max-w-md mx-auto w-full flex-1 flex flex-col">
        <button onClick={onBack} className="self-start p-2 -m-2 mb-6" style={{ color: COLORS.textDark }}>
          <ArrowRight size={22} />
        </button>

        <div className="flex-1 flex flex-col items-center justify-center text-center">
          <IconCircle size={72}>
            <Phone size={30} color="#fff" />
          </IconCircle>
          <h2 className="font-amiri text-2xl font-bold mt-5" style={{ color: COLORS.textDark }}>
            تأكيد الحضور
          </h2>
          <p className="text-sm mt-2" style={{ color: COLORS.mutedText }}>
            أدخل رقم جوالك للتحقق من دعوتك
          </p>

          <div className="w-full mt-8">
            <div className="flex gap-2 items-stretch" dir="ltr">
              <div
                className="rounded-2xl px-4 flex items-center font-bold shrink-0"
                style={{ backgroundColor: COLORS.mutedGold, color: COLORS.textDark }}
              >
                +966
              </div>
              <input
                value={value}
                onChange={(e) => setValue(e.target.value)}
                onBlur={() => setTouched(true)}
                inputMode="numeric"
                placeholder="05xxxxxxxx"
                dir="rtl"
                className="flex-1 rounded-2xl px-4 py-3.5 text-lg text-right outline-none border-2 focus:border-current"
                style={{ backgroundColor: COLORS.card, borderColor: touched && !valid ? COLORS.error : COLORS.mutedGold, color: COLORS.textDark }}
              />
            </div>
            {touched && !valid && (
              <p className="text-xs mt-2 text-right" style={{ color: COLORS.error }}>
                الرجاء إدخال رقم جوال سعودي صحيح (05xxxxxxxx)
              </p>
            )}
          </div>
        </div>

        <div className="mt-8">
          <PrimaryButton onClick={submit} disabled={!valid}>
            متابعة
          </PrimaryButton>
        </div>
      </div>
    </div>
  );
}

function NotFoundScreen({ onRetry }) {
  return (
    <div className="min-h-screen flex flex-col items-center justify-center px-5 py-8 text-center" style={{ backgroundColor: COLORS.cream }}>
      <div className="max-w-md w-full">
        <IconCircle tone="error" size={80} className="mx-auto">
          <XCircle size={38} color="#fff" />
        </IconCircle>
        <h2 className="font-amiri text-2xl font-bold mt-6" style={{ color: COLORS.textDark }}>
          عذراً... هذا الرقم غير موجود
        </h2>
        <p className="text-sm mt-2" style={{ color: COLORS.mutedText }}>
          الرقم غير مسجل ضمن قائمة المدعوين لهذه المناسبة
        </p>
        <div className="mt-8">
          <PrimaryButton onClick={onRetry}>تجربة رقم آخر</PrimaryButton>
        </div>
      </div>
    </div>
  );
}

function RSVPScreen({ guest, onBack, onDecide }) {
  const [selected, setSelected] = useState(null);
  const [locked, setLocked] = useState(false);

  function choose(choice) {
    if (locked) return;
    setSelected(choice);
    setLocked(true);
    setTimeout(() => onDecide(choice), 280);
  }

  const companionsLabel = guest.companions > 0 ? `يُسمح بـ ${guest.companions} مرافقين` : "بدون مرافقين";
  const childrenLabel = guest.children > 0 ? `${guest.children}` : "لا يوجد";

  return (
    <div className="min-h-screen flex flex-col px-5 py-8" style={{ backgroundColor: COLORS.cream }}>
      <div className="max-w-md mx-auto w-full flex-1 flex flex-col">
        <button onClick={onBack} className="self-start p-2 -m-2 mb-4" style={{ color: COLORS.textDark }}>
          <ArrowRight size={22} />
        </button>

        <div className="rounded-3xl p-6 shadow-sm" style={{ backgroundColor: COLORS.card }}>
          <p className="text-xs" style={{ color: COLORS.mutedText }}>
            دعوة خاصة إلى
          </p>
          <h2 className="font-amiri text-2xl font-bold mt-1" style={{ color: COLORS.textDark }}>
            المكرمة {guest.name}
          </h2>
          <div className="my-4 px-4">
            <Ornament />
          </div>
          <div className="space-y-3.5 text-sm">
            <div className="flex items-center gap-3">
              <IconCircle tone="mutedGold" size={34}>
                <Heart size={15} color={COLORS.oliveDark} />
              </IconCircle>
              <div>
                <p style={{ color: COLORS.mutedText }} className="text-xs">
                  المناسبة
                </p>
                <p style={{ color: COLORS.textDark }} className="font-bold">
                  {EVENT.title}
                </p>
              </div>
            </div>
            <div className="flex items-center gap-3">
              <IconCircle tone="mutedGold" size={34}>
                <Calendar size={15} color={COLORS.oliveDark} />
              </IconCircle>
              <div>
                <p style={{ color: COLORS.mutedText }} className="text-xs">
                  التاريخ
                </p>
                <p style={{ color: COLORS.textDark }} className="font-bold">
                  {EVENT.dayName} {EVENT.dateLabel}
                </p>
              </div>
            </div>
            <div className="flex items-center gap-3">
              <IconCircle tone="mutedGold" size={34}>
                <Users size={15} color={COLORS.oliveDark} />
              </IconCircle>
              <div>
                <p style={{ color: COLORS.mutedText }} className="text-xs">
                  المرافقين البالغين
                </p>
                <p style={{ color: COLORS.textDark }} className="font-bold">
                  {companionsLabel}
                </p>
              </div>
            </div>
            <div className="flex items-center gap-3">
              <IconCircle tone="mutedGold" size={34}>
                <Baby size={15} color={COLORS.oliveDark} />
              </IconCircle>
              <div>
                <p style={{ color: COLORS.mutedText }} className="text-xs">
                  الأطفال
                </p>
                <p style={{ color: COLORS.textDark }} className="font-bold">
                  {childrenLabel}
                </p>
              </div>
            </div>
          </div>
        </div>

        <div className="mt-6 grid grid-cols-2 gap-3">
          <button
            onClick={() => choose("confirm")}
            disabled={locked}
            className="rounded-2xl py-6 flex flex-col items-center gap-2 border-2 transition active:scale-[0.98] disabled:active:scale-100"
            style={{
              borderColor: COLORS.olive,
              backgroundColor: selected === "confirm" ? COLORS.olive : "transparent",
            }}
          >
            <Check size={26} color={selected === "confirm" ? "#fff" : COLORS.olive} />
            <span className="font-bold text-sm" style={{ color: selected === "confirm" ? "#fff" : COLORS.olive }}>
              تأكيد الحضور
            </span>
          </button>
          <button
            onClick={() => choose("decline")}
            disabled={locked}
            className="rounded-2xl py-6 flex flex-col items-center gap-2 border-2 transition active:scale-[0.98] disabled:active:scale-100"
            style={{
              borderColor: COLORS.error,
              backgroundColor: selected === "decline" ? COLORS.error : "transparent",
            }}
          >
            <X size={26} color={selected === "decline" ? "#fff" : COLORS.error} />
            <span className="font-bold text-sm" style={{ color: selected === "decline" ? "#fff" : COLORS.error }}>
              اعتذر عن الحضور
            </span>
          </button>
        </div>
      </div>
    </div>
  );
}

function DeclinedScreen({ onBackToInvite }) {
  return (
    <div className="min-h-screen flex flex-col items-center justify-center px-5 py-8 text-center" style={{ backgroundColor: COLORS.cream }}>
      <div className="max-w-md w-full">
        <IconCircle tone="mutedGold" size={80} className="mx-auto">
          <Heart size={36} color={COLORS.oliveDark} />
        </IconCircle>
        <h2 className="font-amiri text-2xl font-bold mt-6" style={{ color: COLORS.textDark }}>
          تم استلام اعتذاركم
        </h2>
        <p className="text-sm mt-2" style={{ color: COLORS.mutedText }}>
          نشكر لكم لطفكم، ونتمنى أن نراكم في مناسبة أخرى قريباً
        </p>
        <div className="mt-8">
          <SecondaryButton onClick={onBackToInvite}>العودة إلى الدعوة</SecondaryButton>
        </div>
      </div>
    </div>
  );
}

// Standard business-card size at 300 DPI (3.5in x 2in).
const BUSINESS_CARD_W = 1050;
const BUSINESS_CARD_H = 600;

function roundedRectPath(ctx, x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.lineTo(x + w - r, y);
  ctx.arcTo(x + w, y, x + w, y + r, r);
  ctx.lineTo(x + w, y + h - r);
  ctx.arcTo(x + w, y + h, x + w - r, y + h, r);
  ctx.lineTo(x + r, y + h);
  ctx.arcTo(x, y + h, x, y + h - r, r);
  ctx.lineTo(x, y + r);
  ctx.arcTo(x, y, x + r, y, r);
  ctx.closePath();
}

function drawExtraCardToCanvas(canvas, guest, cardNumber) {
  const W = BUSINESS_CARD_W;
  const H = BUSINESS_CARD_H;
  canvas.width = W;
  canvas.height = H;
  const ctx = canvas.getContext("2d");
  const ivory = "#F7F0E6";
  const brown = "#5C4632";
  const inset = 10;

  ctx.fillStyle = "#000000";
  ctx.fillRect(0, 0, W, H);

  roundedRectPath(ctx, inset, inset, W - inset * 2, H - inset * 2, 18);
  ctx.fillStyle = ivory;
  ctx.fill();

  ctx.save();
  roundedRectPath(ctx, inset, inset, W - inset * 2, H - inset * 2, 18);
  ctx.clip();
  ctx.strokeStyle = "#EAE0D2";
  ctx.lineWidth = 1;
  for (let y = 20; y < H; y += 58) {
    for (let x = 20; x < W; x += 58) {
      ctx.beginPath();
      ctx.arc(x, y, 3, 0, Math.PI * 2);
      ctx.stroke();
    }
  }
  ctx.restore();

  ctx.strokeStyle = "#D8C9B0";
  ctx.lineWidth = 2;
  ctx.strokeRect(30, 30, W - 60, H - 60);
  ctx.strokeRect(38, 38, W - 76, H - 76);

  const dividerX = 810;
  const columnTop = 40;
  const columnBottom = H - 40;
  ctx.strokeStyle = COLORS.orange;
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.moveTo(dividerX, columnTop);
  ctx.lineTo(dividerX, columnBottom);
  ctx.stroke();

  const qrCenterX = dividerX + (W - dividerX) / 2 - 18;
  const qrSize = 165;
  const labelH = 30;
  const gap = 22;
  const codeH = 30;
  const blockHeight = labelH + gap + (qrSize + 16) + gap + codeH;
  const blockTop = columnTop + (columnBottom - columnTop - blockHeight) / 2;

  ctx.textAlign = "center";
  ctx.fillStyle = brown;
  ctx.font = "bold 22px Tajawal, Arial";
  ctx.fillText("رمز الكود", qrCenterX, blockTop + labelH - 6);

  const qrBoxTop = blockTop + labelH + gap;
  const qrX = qrCenterX - qrSize / 2;
  const qrY = qrBoxTop + 8;
  ctx.fillStyle = "#FFFFFF";
  ctx.fillRect(qrX - 8, qrBoxTop, qrSize + 16, qrSize + 16);
  ctx.strokeStyle = COLORS.orange;
  ctx.lineWidth = 3;
  ctx.strokeRect(qrX - 8, qrBoxTop, qrSize + 16, qrSize + 16);

  const payload = `hala-event://verify?pass=${guest.passCode}&phone=${normalizeSaudiPhone(guest.phone)}`;
  const { matrix, size: modules } = encodeQR(payload);
  const cell = qrSize / modules;
  ctx.fillStyle = "#1A1A1A";
  for (let r = 0; r < modules; r++) {
    for (let c = 0; c < modules; c++) {
      if (matrix[r][c]) ctx.fillRect(qrX + c * cell, qrY + r * cell, Math.ceil(cell), Math.ceil(cell));
    }
  }

  ctx.fillStyle = COLORS.orange;
  ctx.font = "bold 26px Tajawal, Arial";
  ctx.fillText(guest.passCode, qrCenterX, qrBoxTop + (qrSize + 16) + gap + codeH - 6);

  const rightEdge = 780;
  ctx.textAlign = "right";
  ctx.fillStyle = COLORS.orange;
  ctx.font = "bold 30px Tajawal, Arial";
  ctx.fillText(`${EVENT.dayName} ${EVENT.dateLabel}  ·  ${EVENT.venue}`, rightEdge, 75);

  const leftCenterX = (60 + rightEdge) / 2;
  ctx.textAlign = "center";
  ctx.fillStyle = brown;
  ctx.font = "20px Tajawal, Arial";
  ctx.fillText("اسم الضيف", leftCenterX, 165);

  ctx.fillStyle = COLORS.textDark;
  ctx.font = guest.name ? "bold 40px Tajawal, Arial" : "bold 56px Tajawal, Arial";
  ctx.fillText(guest.name || "—", leftCenterX, 235);

  ctx.fillStyle = brown;
  ctx.font = "20px Tajawal, Arial";
  const infoLine = `الجوال: ${formatDisplayPhone(guest.phone) || "—"}   ·   بالغين: ${guest.companions}   ·   أطفال: ${guest.children}`;
  ctx.fillText(infoLine, leftCenterX, 300);

  ctx.strokeStyle = COLORS.orange;
  ctx.lineWidth = 1.5;
  ctx.beginPath();
  ctx.moveTo(60, 335);
  ctx.lineTo(rightEdge, 335);
  ctx.stroke();

  ctx.textAlign = "center";
  ctx.fillStyle = brown;
  ctx.font = "20px Tajawal, Arial";
  ctx.fillText("رقم الكرت", leftCenterX, 395);

  ctx.fillStyle = COLORS.orange;
  ctx.font = "bold 150px Tajawal, Arial";
  ctx.fillText(String(cardNumber), leftCenterX, 545);

  return canvas;
}

function ImagePreviewModal({ dataUrl, onClose }) {
  return (
    <div className="fixed inset-0 z-[60] bg-black flex flex-col">
      <div className="flex justify-between items-center px-4 py-3" style={{ backgroundColor: COLORS.oliveDark }}>
        <button onClick={onClose} className="text-white p-2 -m-2">
          <X size={22} />
        </button>
        <span className="text-white text-sm font-bold">اضغط مطوّلاً على الصورة واختر "حفظ الصورة"</span>
        <span className="w-6" />
      </div>
      <div className="flex-1 overflow-auto flex items-center justify-center p-4">
        <img src={dataUrl} alt="بطاقة الدخول" className="max-w-full rounded-2xl shadow-2xl" />
      </div>
      <div className="p-4">
        <a
          href={dataUrl}
          target="_blank"
          rel="noreferrer"
          className="w-full rounded-2xl py-3 font-bold text-sm flex items-center justify-center gap-2"
          style={{ backgroundColor: COLORS.gold, color: COLORS.oliveDark }}
        >
          <ExternalLink size={16} />
          فتح الصورة في تبويب جديد
        </a>
      </div>
    </div>
  );
}

function ThankYouModal({ guest, onClose, onSend }) {
  const [text, setText] = useState("");
  const [sent, setSent] = useState(false);

  function send() {
    if (!text.trim()) return;
    onSend(text.trim());
    setSent(true);
  }

  if (sent) {
    return (
      <Modal onClose={onClose}>
        <div className="text-center py-4">
          <div className="mx-auto flex items-center justify-center animate-heartbeat" style={{ width: 72, height: 72 }}>
            <Heart size={56} color={COLORS.error} fill={COLORS.error} />
          </div>
          <h3 className="font-amiri text-xl font-bold mt-5" style={{ color: COLORS.textDark }}>
            تم إرسال رسالتك بنجاح
          </h3>
          <p className="text-sm mt-1" style={{ color: COLORS.mutedText }}>
            شكراً لذوقك الجميل
          </p>
          <div className="mt-6">
            <PrimaryButton onClick={onClose}>تم</PrimaryButton>
          </div>
        </div>
      </Modal>
    );
  }

  return (
    <Modal onClose={onClose}>
      <h3 className="font-amiri text-xl font-bold text-center" style={{ color: COLORS.textDark }}>
        إرسال رسالة شكر
      </h3>
      <p className="text-xs text-center mt-1 mb-4" style={{ color: COLORS.mutedText }}>
        اترك كلمة أو تهنئة للعروسين
      </p>
      <textarea
        value={text}
        onChange={(e) => setText(e.target.value)}
        rows={4}
        placeholder="اكتب تهنئتك هنا..."
        className="w-full rounded-2xl p-4 text-sm outline-none border-2 resize-none"
        style={{ backgroundColor: COLORS.cream, borderColor: COLORS.mutedGold, color: COLORS.textDark }}
      />
      <div className="mt-4">
        <PrimaryButton onClick={send} disabled={!text.trim()}>
          <span className="flex items-center justify-center gap-2">
            <Send size={16} />
            إرسال
          </span>
        </PrimaryButton>
      </div>
    </Modal>
  );
}

function PassScreen({ guest, onOpenThankYou }) {
  const [previewUrl, setPreviewUrl] = useState(null);
  const canvasRef = useRef(null);

  const cardImageUrl = useMemo(() => {
    const canvas = document.createElement("canvas");
    drawExtraCardToCanvas(canvas, guest, guest.id);
    return canvas.toDataURL("image/png");
  }, [guest]);

  function handleDownload() {
    if (!canvasRef.current) canvasRef.current = document.createElement("canvas");
    drawExtraCardToCanvas(canvasRef.current, guest, guest.id);
    const dataUrl = canvasRef.current.toDataURL("image/png");
    try {
      const a = document.createElement("a");
      a.href = dataUrl;
      a.download = `pass-${normalizePassCode(guest.passCode)}.png`;
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
    } catch (e) {
      /* ignore — the preview modal below is the guaranteed save path */
    }
    setPreviewUrl(dataUrl);
  }

  return (
    <div className="min-h-screen flex flex-col items-center px-5 py-10" style={{ backgroundColor: COLORS.cream }}>
      <div className="max-w-md w-full">
        <img
          src={cardImageUrl}
          alt="بطاقة الدخول"
          className="w-full rounded-2xl shadow-xl"
          style={{ aspectRatio: `${BUSINESS_CARD_W} / ${BUSINESS_CARD_H}` }}
        />

        <div className="mt-6 space-y-3">
          <SecondaryButton onClick={handleDownload}>
            <Download size={18} />
            تحميل البطاقة
          </SecondaryButton>
          <PrimaryButton onClick={onOpenThankYou}>إرسال رسالة شكر</PrimaryButton>
        </div>
      </div>

      {previewUrl && <ImagePreviewModal dataUrl={previewUrl} onClose={() => setPreviewUrl(null)} />}
    </div>
  );
}

/* ---------- admin ---------- */

function AdminLockScreen({ onUnlock, onBack }) {
  const [pwd, setPwd] = useState("");
  const [error, setError] = useState(false);

  function submit(e) {
    e.preventDefault();
    if (pwd === ADMIN_PASSWORD) onUnlock();
    else {
      setError(true);
      setPwd("");
    }
  }

  return (
    <div className="min-h-screen flex flex-col items-center justify-center px-5 py-8" style={{ backgroundColor: COLORS.cream }}>
      <div className="max-w-sm w-full text-center">
        <IconCircle size={72} className="mx-auto">
          <Lock size={30} color="#fff" />
        </IconCircle>
        <h2 className="font-amiri text-xl font-bold mt-5" style={{ color: COLORS.textDark }}>
          أدخل كلمة السر للمتابعة
        </h2>
        <form onSubmit={submit} className="mt-6">
          <input
            type="password"
            inputMode="numeric"
            value={pwd}
            onChange={(e) => {
              setPwd(e.target.value);
              setError(false);
            }}
            autoFocus
            className="w-full text-center tracking-[0.4em] rounded-2xl px-4 py-3.5 text-lg outline-none border-2"
            style={{ backgroundColor: COLORS.card, borderColor: error ? COLORS.error : COLORS.mutedGold, color: COLORS.textDark }}
          />
          {error && (
            <p className="text-xs mt-2" style={{ color: COLORS.error }}>
              كلمة السر غير صحيحة
            </p>
          )}
          <div className="mt-6 space-y-3">
            <PrimaryButton type="submit">دخول</PrimaryButton>
            <SecondaryButton onClick={onBack}>العودة للدعوة</SecondaryButton>
          </div>
        </form>
        <p className="text-[11px] mt-6" style={{ color: COLORS.mutedText }}>
          هذه بوابة حماية بسيطة من جهة المتصفح فقط لأغراض العرض التوضيحي — في الإنتاج يجب استخدام مصادقة حقيقية من الخادم (مثل Supabase Auth).
        </p>
      </div>
    </div>
  );
}

function ScanLockScreen({ onUnlock, onBack }) {
  const [pwd, setPwd] = useState("");
  const [error, setError] = useState(false);

  function submit(e) {
    e.preventDefault();
    if (pwd === SCAN_PASSWORD) onUnlock();
    else {
      setError(true);
      setPwd("");
    }
  }

  return (
    <div className="min-h-screen flex flex-col items-center justify-center px-5 py-8" style={{ backgroundColor: COLORS.cream }}>
      <div className="max-w-sm w-full text-center">
        <IconCircle size={72} className="mx-auto">
          <ScanLine size={30} color="#fff" />
        </IconCircle>
        <h2 className="font-amiri text-xl font-bold mt-5" style={{ color: COLORS.textDark }}>
          أدخل كلمة السر لمسح الباركود
        </h2>
        <form onSubmit={submit} className="mt-6">
          <input
            type="password"
            inputMode="numeric"
            value={pwd}
            onChange={(e) => {
              setPwd(e.target.value);
              setError(false);
            }}
            autoFocus
            className="w-full text-center tracking-[0.4em] rounded-2xl px-4 py-3.5 text-lg outline-none border-2"
            style={{ backgroundColor: COLORS.card, borderColor: error ? COLORS.error : COLORS.mutedGold, color: COLORS.textDark }}
          />
          {error && (
            <p className="text-xs mt-2" style={{ color: COLORS.error }}>
              كلمة السر غير صحيحة
            </p>
          )}
          <div className="mt-6 space-y-3">
            <PrimaryButton type="submit">دخول</PrimaryButton>
            <SecondaryButton onClick={onBack}>العودة للدعوة</SecondaryButton>
          </div>
        </form>
      </div>
    </div>
  );
}

function ScanPage({ guests, setGuests, onExit }) {
  return (
    <div className="min-h-screen" style={{ backgroundColor: COLORS.cream }}>
      <div className="px-5 py-5 max-w-lg mx-auto">
        <div className="flex items-center justify-between mb-5">
          <h1 className="font-amiri text-2xl font-bold" style={{ color: COLORS.textDark }}>
            مسح الباركود
          </h1>
          <button
            onClick={onExit}
            className="rounded-full px-4 py-2 text-xs font-bold"
            style={{ backgroundColor: COLORS.oliveDark, color: COLORS.cream }}
          >
            العودة للدعوة
          </button>
        </div>
        <ScanTab guests={guests} setGuests={setGuests} />
      </div>
    </div>
  );
}

function GuestFormModal({ initial, onClose, onSave }) {
  const [name, setName] = useState(initial?.name || "");
  const [phone, setPhone] = useState(initial?.phone || "");
  const [companions, setCompanions] = useState(initial?.companions ?? 0);
  const [children, setChildren] = useState(initial?.children ?? 0);
  const [phonePolicy, setPhonePolicy] = useState(initial?.phonePolicy || "");
  const [errors, setErrors] = useState({});

  function submit() {
    const errs = {};
    if (!name.trim()) errs.name = "الاسم مطلوب";
    if (!isValidSaudiPhone(phone)) errs.phone = "رقم جوال سعودي غير صحيح";
    if (companions < 0) errs.companions = "عدد غير صحيح";
    if (children < 0) errs.children = "عدد غير صحيح";
    setErrors(errs);
    if (Object.keys(errs).length > 0) return;
    onSave({
      name: name.trim(),
      phone: normalizeSaudiPhone(phone),
      companions: Number(companions) || 0,
      children: Number(children) || 0,
      phonePolicy: phonePolicy || null,
    });
  }

  return (
    <Modal onClose={onClose}>
      <h3 className="font-amiri text-xl font-bold text-center" style={{ color: COLORS.textDark }}>
        {initial ? "تعديل بيانات الضيف" : "إضافة ضيف"}
      </h3>
      <div className="mt-5 space-y-4">
        <div>
          <label className="text-xs font-bold" style={{ color: COLORS.mutedText }}>
            الاسم
          </label>
          <input
            value={name}
            onChange={(e) => setName(e.target.value)}
            className="w-full mt-1 rounded-xl px-3.5 py-2.5 outline-none border-2"
            style={{ backgroundColor: COLORS.cream, borderColor: errors.name ? COLORS.error : COLORS.mutedGold, color: COLORS.textDark }}
          />
          {errors.name && (
            <p className="text-xs mt-1" style={{ color: COLORS.error }}>
              {errors.name}
            </p>
          )}
        </div>
        <div>
          <label className="text-xs font-bold" style={{ color: COLORS.mutedText }}>
            رقم الجوال
          </label>
          <input
            value={phone}
            onChange={(e) => setPhone(e.target.value)}
            inputMode="numeric"
            placeholder="05xxxxxxxx"
            dir="ltr"
            className="w-full mt-1 rounded-xl px-3.5 py-2.5 outline-none border-2 text-right"
            style={{ backgroundColor: COLORS.cream, borderColor: errors.phone ? COLORS.error : COLORS.mutedGold, color: COLORS.textDark }}
          />
          {errors.phone && (
            <p className="text-xs mt-1" style={{ color: COLORS.error }}>
              {errors.phone}
            </p>
          )}
        </div>
        <div className="grid grid-cols-2 gap-3">
          <div>
            <label className="text-xs font-bold" style={{ color: COLORS.mutedText }}>
              عدد المرافقين البالغين
            </label>
            <input
              type="number"
              min={0}
              value={companions}
              onChange={(e) => setCompanions(e.target.value)}
              className="w-full mt-1 rounded-xl px-3.5 py-2.5 outline-none border-2"
              style={{ backgroundColor: COLORS.cream, borderColor: COLORS.mutedGold, color: COLORS.textDark }}
            />
          </div>
          <div>
            <label className="text-xs font-bold" style={{ color: COLORS.mutedText }}>
              عدد الأطفال
            </label>
            <input
              type="number"
              min={0}
              value={children}
              onChange={(e) => setChildren(e.target.value)}
              className="w-full mt-1 rounded-xl px-3.5 py-2.5 outline-none border-2"
              style={{ backgroundColor: COLORS.cream, borderColor: COLORS.mutedGold, color: COLORS.textDark }}
            />
          </div>
        </div>
        <div>
          <label className="text-xs font-bold" style={{ color: COLORS.mutedText }}>
            إجراء الجوال عند الدخول
          </label>
          <select
            value={phonePolicy}
            onChange={(e) => setPhonePolicy(e.target.value)}
            className="w-full mt-1 rounded-xl px-3.5 py-2.5 outline-none border-2"
            style={{ backgroundColor: COLORS.cream, borderColor: COLORS.mutedGold, color: COLORS.textDark }}
          >
            <option value="">بدون تحديد</option>
            {Object.entries(PHONE_POLICIES).map(([key, p]) => (
              <option key={key} value={key}>
                {p.label}
              </option>
            ))}
          </select>
          <p className="text-[11px] mt-1" style={{ color: COLORS.mutedText }}>
            يظهر هذا فقط للفريق عند مسح الباركود، ولا يظهر للضيف
          </p>
        </div>
      </div>
      <div className="mt-6 grid grid-cols-2 gap-3">
        <SecondaryButton onClick={onClose}>إلغاء</SecondaryButton>
        <PrimaryButton onClick={submit}>حفظ</PrimaryButton>
      </div>
    </Modal>
  );
}

function DeleteConfirmModal({ guest, onCancel, onConfirm }) {
  return (
    <Modal onClose={onCancel}>
      <div className="text-center">
        <IconCircle tone="error" size={60} className="mx-auto">
          <Trash2 size={26} color="#fff" />
        </IconCircle>
        <h3 className="font-amiri text-lg font-bold mt-4" style={{ color: COLORS.textDark }}>
          حذف الضيف؟
        </h3>
        <p className="text-sm mt-1" style={{ color: COLORS.mutedText }}>
          سيتم حذف "{guest.name}" نهائياً من قائمة المدعوين
        </p>
        <div className="mt-6 grid grid-cols-2 gap-3">
          <SecondaryButton onClick={onCancel}>إلغاء</SecondaryButton>
          <button
            onClick={onConfirm}
            className="w-full rounded-2xl py-3.5 font-bold text-base text-white transition active:scale-[0.98]"
            style={{ backgroundColor: COLORS.error }}
          >
            حذف
          </button>
        </div>
      </div>
    </Modal>
  );
}

function StatCard({ label, value, onClick, active }) {
  const Tag = onClick ? "button" : "div";
  return (
    <Tag
      onClick={onClick}
      type={onClick ? "button" : undefined}
      className={`rounded-2xl p-3.5 text-center transition w-full ${onClick ? "active:scale-[0.97]" : ""}`}
      style={{
        backgroundColor: COLORS.card,
        border: `2px solid ${active ? COLORS.olive : "transparent"}`,
      }}
    >
      <p className="text-2xl font-bold" style={{ color: COLORS.olive }}>
        {value}
      </p>
      <p className="text-[11px] mt-0.5" style={{ color: COLORS.mutedText }}>
        {label}
      </p>
    </Tag>
  );
}

function StatusBreakdownChart({ confirmed, declined, pending }) {
  const total = confirmed + declined + pending;
  const segments = [
    { key: "confirmed", label: "مؤكدين", value: confirmed, color: COLORS.olive, textOn: "#fff" },
    { key: "pending", label: "بانتظار الرد", value: pending, color: COLORS.mutedGold, textOn: COLORS.textDark },
    { key: "declined", label: "معتذرين", value: declined, color: COLORS.error, textOn: "#fff" },
  ].map((s) => ({ ...s, pct: total > 0 ? (s.value / total) * 100 : 0 }));

  return (
    <div className="rounded-2xl p-4 mb-5" style={{ backgroundColor: COLORS.card }}>
      <p className="text-xs font-bold mb-3" style={{ color: COLORS.mutedText }}>
        نسبة حالات الحضور
      </p>
      <div
        className="flex w-full rounded-full overflow-hidden"
        style={{ height: 28, gap: 2, backgroundColor: COLORS.cream }}
      >
        {segments.map(
          (s) =>
            s.value > 0 && (
              <div
                key={s.key}
                className="flex items-center justify-center"
                style={{ width: `${s.pct}%`, backgroundColor: s.color }}
              >
                {s.pct >= 12 && (
                  <span className="text-[11px] font-bold" style={{ color: s.textOn }}>
                    {Math.round(s.pct)}%
                  </span>
                )}
              </div>
            )
        )}
      </div>
      <div className="flex flex-wrap gap-x-5 gap-y-2 mt-3">
        {segments.map((s) => (
          <div key={s.key} className="flex items-center gap-1.5 text-xs">
            <span className="inline-block rounded-full shrink-0" style={{ width: 8, height: 8, backgroundColor: s.color }} />
            <span style={{ color: COLORS.textDark }}>
              {s.label}{" "}
              <span style={{ color: COLORS.mutedText }}>
                ({s.value} · {Math.round(s.pct)}%)
              </span>
            </span>
          </div>
        ))}
      </div>
    </div>
  );
}

function GuestListTab({ guests, setGuests }) {
  const [query, setQuery] = useState("");
  const [formGuest, setFormGuest] = useState(undefined); // undefined=closed, null=new, object=edit
  const [deleteGuest, setDeleteGuest] = useState(null);
  const [statusFilter, setStatusFilter] = useState(null); // null|confirmed|declined|pending

  const regularGuests = guests.filter((g) => !g.isExtraCard);

  const stats = {
    total: regularGuests.length,
    confirmed: regularGuests.filter((g) => g.status === "confirmed").length,
    declined: regularGuests.filter((g) => g.status === "declined").length,
    pending: regularGuests.filter((g) => g.status === "pending").length,
    checkedIn: regularGuests.filter((g) => g.checkedIn).length,
  };

  const statusFilterLabel = { confirmed: "المؤكدين", declined: "المعتذرين", pending: "بانتظار الرد" }[statusFilter];

  function toggleStatusFilter(status) {
    setStatusFilter((f) => (f === status ? null : status));
  }

  const filtered = regularGuests.filter((g) => {
    if (statusFilter && g.status !== statusFilter) return false;
    const q = query.trim();
    if (!q) return true;
    return g.name.includes(q) || g.phone.includes(q);
  });

  function saveGuest(data) {
    if (formGuest && formGuest.id) {
      setGuests((prev) => prev.map((g) => (g.id === formGuest.id ? { ...g, ...data } : g)));
    } else {
      const nextId = regularGuests.length ? Math.max(...regularGuests.map((g) => g.id)) + 1 : 101;
      setGuests((prev) => [...prev, { id: nextId, status: "pending", checkedIn: false, passCode: generatePassCode(), ...data }]);
    }
    setFormGuest(undefined);
  }

  function toggleCheckIn(id) {
    setGuests((prev) => prev.map((g) => (g.id === id ? { ...g, checkedIn: !g.checkedIn } : g)));
  }

  return (
    <div>
      <div className="grid grid-cols-5 gap-2 mb-5">
        <StatCard label="الإجمالي" value={stats.total} />
        <StatCard
          label="مؤكدين"
          value={stats.confirmed}
          active={statusFilter === "confirmed"}
          onClick={() => toggleStatusFilter("confirmed")}
        />
        <StatCard
          label="معتذرين"
          value={stats.declined}
          active={statusFilter === "declined"}
          onClick={() => toggleStatusFilter("declined")}
        />
        <StatCard
          label="بانتظار الرد"
          value={stats.pending}
          active={statusFilter === "pending"}
          onClick={() => toggleStatusFilter("pending")}
        />
        <StatCard label="تسجيل دخول" value={stats.checkedIn} />
      </div>

      <StatusBreakdownChart confirmed={stats.confirmed} declined={stats.declined} pending={stats.pending} />

      {statusFilter && (
        <div
          className="flex items-center justify-between rounded-xl px-3.5 py-2.5 mb-4 text-xs font-bold"
          style={{ backgroundColor: COLORS.mutedGold, color: COLORS.textDark }}
        >
          <span>عرض: {statusFilterLabel} فقط</span>
          <button onClick={() => setStatusFilter(null)} className="underline">
            إظهار الكل
          </button>
        </div>
      )}

      <div className="flex gap-2 mb-4">
        <div className="relative flex-1">
          <Search size={16} className="absolute top-1/2 -translate-y-1/2 right-3" style={{ color: COLORS.mutedText }} />
          <input
            value={query}
            onChange={(e) => setQuery(e.target.value)}
            placeholder="بحث بالاسم أو الجوال"
            className="w-full rounded-xl pr-9 pl-3 py-2.5 text-sm outline-none border-2"
            style={{ backgroundColor: COLORS.card, borderColor: COLORS.mutedGold, color: COLORS.textDark }}
          />
        </div>
        <button
          onClick={() => setFormGuest(null)}
          className="rounded-xl px-4 flex items-center gap-1.5 font-bold text-sm text-white shrink-0"
          style={{ backgroundColor: COLORS.olive }}
        >
          <Plus size={16} />
          إضافة ضيف
        </button>
      </div>

      <div className="rounded-2xl overflow-hidden" style={{ backgroundColor: COLORS.card }}>
        <div className="overflow-x-auto">
          <table className="w-full text-sm">
            <thead>
              <tr style={{ backgroundColor: COLORS.mutedGold }}>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  الاسم
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  رمز البطاقة
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  الجوال
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  المرافقين البالغين
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  الأطفال
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  الحالة
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  حالة الجوال
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  دخول
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}></th>
              </tr>
            </thead>
            <tbody>
              {filtered.map((g) => (
                <tr key={g.id} className="border-t" style={{ borderColor: COLORS.mutedGold }}>
                  <td className="px-3 py-2.5 font-bold whitespace-nowrap" style={{ color: COLORS.textDark }}>
                    {g.name}
                  </td>
                  <td className="px-3 py-2.5 whitespace-nowrap tracking-wider" style={{ color: COLORS.mutedText }} dir="ltr">
                    {g.passCode}
                  </td>
                  <td className="px-3 py-2.5 whitespace-nowrap" style={{ color: COLORS.mutedText }} dir="ltr">
                    {formatDisplayPhone(g.phone)}
                  </td>
                  <td className="px-3 py-2.5" style={{ color: COLORS.textDark }}>
                    {g.companions}
                  </td>
                  <td className="px-3 py-2.5" style={{ color: COLORS.textDark }}>
                    {g.children}
                  </td>
                  <td className="px-3 py-2.5">
                    <StatusPill status={g.status} />
                  </td>
                  <td className="px-3 py-2.5">
                    <PhonePolicyPill value={g.phonePolicy} />
                  </td>
                  <td className="px-3 py-2.5">
                    <button
                      onClick={() => toggleCheckIn(g.id)}
                      disabled={g.status !== "confirmed"}
                      className="rounded-lg px-2.5 py-1.5 text-xs font-bold whitespace-nowrap disabled:opacity-40"
                      style={{
                        backgroundColor: g.checkedIn ? COLORS.olive : COLORS.mutedGold,
                        color: g.checkedIn ? "#fff" : COLORS.textDark,
                      }}
                    >
                      {g.checkedIn ? "تم الدخول" : "تأكيد الدخول"}
                    </button>
                  </td>
                  <td className="px-3 py-2.5">
                    <div className="flex gap-1.5">
                      <button onClick={() => setFormGuest(g)} className="p-1.5 rounded-lg" style={{ color: COLORS.olive }}>
                        <Pencil size={15} />
                      </button>
                      <button onClick={() => setDeleteGuest(g)} className="p-1.5 rounded-lg" style={{ color: COLORS.error }}>
                        <Trash2 size={15} />
                      </button>
                    </div>
                  </td>
                </tr>
              ))}
              {filtered.length === 0 && (
                <tr>
                  <td colSpan={9} className="px-3 py-8 text-center" style={{ color: COLORS.mutedText }}>
                    لا يوجد نتائج
                  </td>
                </tr>
              )}
            </tbody>
          </table>
        </div>
      </div>

      {formGuest !== undefined && (
        <GuestFormModal initial={formGuest} onClose={() => setFormGuest(undefined)} onSave={saveGuest} />
      )}
      {deleteGuest && (
        <DeleteConfirmModal
          guest={deleteGuest}
          onCancel={() => setDeleteGuest(null)}
          onConfirm={() => {
            setGuests((prev) => prev.filter((g) => g.id !== deleteGuest.id));
            setDeleteGuest(null);
          }}
        />
      )}
    </div>
  );
}

function parsePassCode(raw) {
  const s = String(raw || "").trim();
  if (!s) return null;
  const m = s.match(/pass=([A-Za-z0-9-]+)/);
  return m ? m[1] : s;
}

function CameraScannerModal({ guests, onClose, onResult }) {
  const videoRef = useRef(null);
  const streamRef = useRef(null);
  const rafRef = useRef(null);
  const [state, setState] = useState("requesting"); // requesting | active | error
  const [errorType, setErrorType] = useState(null); // unsupported | permission | generic

  useEffect(() => {
    let cancelled = false;

    async function start() {
      if (!("BarcodeDetector" in window)) {
        setErrorType("unsupported");
        setState("error");
        return;
      }
      if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
        setErrorType("unsupported");
        setState("error");
        return;
      }
      try {
        const stream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: { ideal: "environment" } } });
        if (cancelled) {
          stream.getTracks().forEach((t) => t.stop());
          return;
        }
        streamRef.current = stream;
        if (videoRef.current) {
          videoRef.current.srcObject = stream;
          await videoRef.current.play();
        }
        setState("active");
        const detector = new window.BarcodeDetector({ formats: ["qr_code"] });

        const tick = async () => {
          if (cancelled || !videoRef.current) return;
          try {
            const codes = await detector.detect(videoRef.current);
            if (codes && codes.length > 0) {
              const passCode = parsePassCode(codes[0].rawValue);
              const guest = passCode
                ? guests.find((g) => normalizePassCode(g.passCode) === normalizePassCode(passCode))
                : null;
              onResult({ passCode, guest, raw: codes[0].rawValue });
              return;
            }
          } catch (e) {
            /* transient detection errors are ignored, polling continues */
          }
          rafRef.current = requestAnimationFrame(tick);
        };
        rafRef.current = requestAnimationFrame(tick);
      } catch (e) {
        if (cancelled) return;
        if (e && (e.name === "NotAllowedError" || e.name === "PermissionDeniedError")) setErrorType("permission");
        else setErrorType("generic");
        setState("error");
      }
    }

    start();
    return () => {
      cancelled = true;
      if (rafRef.current) cancelAnimationFrame(rafRef.current);
      if (streamRef.current) streamRef.current.getTracks().forEach((t) => t.stop());
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  return (
    <div className="fixed inset-0 z-[60] bg-black flex flex-col">
      <div className="flex justify-between items-center px-4 py-3">
        <button onClick={onClose} className="text-white p-2 -m-2">
          <X size={22} />
        </button>
        <span className="text-white text-sm font-bold">مسح باركود الدخول</span>
        <span className="w-6" />
      </div>

      {state === "requesting" && (
        <div className="flex-1 flex flex-col items-center justify-center gap-3 text-white px-6 text-center">
          <Loader2 size={32} className="animate-spin" />
          <p className="text-sm">جاري تشغيل الكاميرا...</p>
        </div>
      )}

      {state === "active" && (
        <div className="flex-1 relative overflow-hidden">
          <video ref={videoRef} className="w-full h-full object-cover" playsInline muted />
          <div className="absolute inset-0 flex items-center justify-center pointer-events-none">
            <div className="w-64 h-64 rounded-2xl" style={{ border: `3px solid ${COLORS.gold}` }} />
          </div>
        </div>
      )}
      {/* the video element must exist for the requesting phase too so getUserMedia can attach on time */}
      {state === "requesting" && <video ref={videoRef} className="hidden" playsInline muted />}

      {state === "error" && (
        <div className="flex-1 flex flex-col items-center justify-center gap-3 text-white px-6 text-center">
          <IconCircle tone="error" size={64}>
            <AlertCircle size={28} color="#fff" />
          </IconCircle>
          {errorType === "unsupported" && (
            <p className="text-sm">
              الكاميرا أو خاصية قراءة الباركود غير مدعومة في هذا المتصفح. الرجاء استخدام الإدخال اليدوي أدناه.
            </p>
          )}
          {errorType === "permission" && (
            <p className="text-sm">
              تم رفض إذن الكاميرا. قد يكون هذا بسبب قيود المتصفح المدمج داخل التطبيق (in-app WebView) وليس بالضرورة رفضاً
              مقصوداً منك — جرّب فتح الصفحة في متصفح حقيقي مثل Chrome أو Safari.
            </p>
          )}
          {errorType === "generic" && <p className="text-sm">حدث خطأ أثناء تشغيل الكاميرا. الرجاء المحاولة مرة أخرى.</p>}
          <div className="w-full max-w-xs mt-2">
            <PrimaryButton onClick={onClose}>استخدام الإدخال اليدوي</PrimaryButton>
          </div>
        </div>
      )}
    </div>
  );
}

function ScanTab({ guests, setGuests }) {
  const [cameraOpen, setCameraOpen] = useState(false);
  const [manualValue, setManualValue] = useState("");
  const [result, setResult] = useState(null); // { passCode, guest, raw }
  const [notFound, setNotFound] = useState(false);
  const [justConfirmed, setJustConfirmed] = useState(false);

  function handleManualSearch() {
    setNotFound(false);
    setJustConfirmed(false);
    const passCode = parsePassCode(manualValue);
    const guest = passCode
      ? guests.find((g) => normalizePassCode(g.passCode) === normalizePassCode(passCode))
      : null;
    if (guest) setResult({ passCode, guest });
    else {
      setResult(null);
      setNotFound(true);
    }
  }

  function handleCameraResult({ passCode, guest }) {
    setCameraOpen(false);
    setNotFound(false);
    setJustConfirmed(false);
    if (guest) setResult({ passCode, guest });
    else {
      setResult(null);
      setNotFound(true);
    }
  }

  function confirmCheckIn(id) {
    setGuests((prev) => prev.map((g) => (g.id === id ? { ...g, checkedIn: true } : g)));
    setResult((r) => (r && r.guest ? { ...r, guest: { ...r.guest, checkedIn: true } } : r));
    setJustConfirmed(true);
  }

  return (
    <div>
      <button
        onClick={() => {
          setCameraOpen(true);
          setResult(null);
          setNotFound(false);
        }}
        className="w-full rounded-2xl py-4 flex items-center justify-center gap-2 font-bold text-white mb-4"
        style={{ backgroundColor: COLORS.olive }}
      >
        <Camera size={20} />
        فتح الكاميرا لمسح الباركود
      </button>

      <div className="rounded-2xl p-4 mb-4" style={{ backgroundColor: COLORS.card }}>
        <p className="text-xs font-bold mb-2" style={{ color: COLORS.mutedText }}>
          أو أدخل رقم البطاقة يدوياً
        </p>
        <div className="flex gap-2">
          <input
            value={manualValue}
            onChange={(e) => setManualValue(e.target.value)}
            placeholder="مثال: 7F3K-9B2A أو hala-event://verify?pass=7F3K-9B2A..."
            className="flex-1 rounded-xl px-3 py-2.5 text-sm outline-none border-2"
            style={{ backgroundColor: COLORS.cream, borderColor: COLORS.mutedGold, color: COLORS.textDark }}
          />
          <button
            onClick={handleManualSearch}
            className="rounded-xl px-4 font-bold text-sm text-white shrink-0"
            style={{ backgroundColor: COLORS.oliveDark }}
          >
            بحث
          </button>
        </div>
      </div>

      {notFound && (
        <div className="rounded-2xl p-4 flex items-center gap-2 text-sm" style={{ backgroundColor: COLORS.mutedGold, color: COLORS.error }}>
          <AlertCircle size={16} />
          لم يتم العثور على بطاقة بهذا الرقم
        </div>
      )}

      {result &&
        result.guest &&
        (() => {
          const g = result.guest;
          const big = justConfirmed
            ? { color: COLORS.olive, Icon: CheckCircle2, label: "تم تأكيد الدخول", emphasize: true }
            : g.checkedIn
              ? { color: COLORS.error, Icon: XCircle, label: "تم الدخول مسبقًا بهذا الكود" }
              : g.status !== "confirmed"
                ? {
                    color: COLORS.error,
                    Icon: XCircle,
                    label: g.status === "declined" ? "الضيف اعتذر عن الحضور" : "لم يتم تأكيد الحضور بعد",
                  }
                : { color: COLORS.olive, Icon: CheckCircle2, label: "الكود فعال — يمكن الدخول" };
          return (
            <div className="rounded-2xl p-5" style={{ backgroundColor: COLORS.card }}>
              <div className="flex flex-col items-center text-center mb-5">
                <big.Icon size={big.emphasize ? 120 : 100} color={big.color} strokeWidth={1.5} />
                <p className={`font-bold mt-2 ${big.emphasize ? "text-2xl" : "text-lg"}`} style={{ color: big.color }}>
                  {big.label}
                </p>
              </div>
              <div className="flex items-center gap-3 mb-4">
                <IconCircle tone={g.status === "confirmed" ? "olive" : "error"} size={44}>
                  {g.status === "confirmed" ? <CheckCircle2 size={20} color="#fff" /> : <XCircle size={20} color="#fff" />}
                </IconCircle>
                <div>
                  <p className="font-bold" style={{ color: COLORS.textDark }}>
                    {g.name || "بطاقة إضافية بدون اسم"}
                    {g.isExtraCard && (
                      <span className="text-xs font-normal mr-1" style={{ color: COLORS.mutedText }}>
                        (كرت إضافي)
                      </span>
                    )}
                  </p>
                  <StatusPill status={g.status} />
                </div>
              </div>
              <PhonePolicyCallout value={g.phonePolicy} />
              <div className="space-y-2 text-sm mb-4">
                <div className="flex justify-between">
                  <span style={{ color: COLORS.mutedText }}>رمز البطاقة</span>
                  <span dir="ltr" className="font-bold tracking-wider" style={{ color: COLORS.textDark }}>
                    {g.passCode}
                  </span>
                </div>
                <div className="flex justify-between">
                  <span style={{ color: COLORS.mutedText }}>الجوال</span>
                  <span dir="ltr" style={{ color: COLORS.textDark }}>
                    {formatDisplayPhone(g.phone) || "—"}
                  </span>
                </div>
                <div className="flex justify-between">
                  <span style={{ color: COLORS.mutedText }}>المرافقين البالغين</span>
                  <span style={{ color: COLORS.textDark }}>{g.companions}</span>
                </div>
                <div className="flex justify-between">
                  <span style={{ color: COLORS.mutedText }}>الأطفال</span>
                  <span style={{ color: COLORS.textDark }}>{g.children}</span>
                </div>
              </div>
              <PrimaryButton onClick={() => confirmCheckIn(g.id)} disabled={g.checkedIn || g.status !== "confirmed"}>
                <span className="flex items-center justify-center gap-2">
                  <LogIn size={16} />
                  {justConfirmed ? "تم تأكيد الدخول" : g.checkedIn ? "تم الدخول مسبقاً" : "تأكيد الدخول"}
                </span>
              </PrimaryButton>
            </div>
          );
        })()}

      {cameraOpen && <CameraScannerModal guests={guests} onClose={() => setCameraOpen(false)} onResult={handleCameraResult} />}
    </div>
  );
}

function MessagesTab({ messages }) {
  return (
    <div className="space-y-3">
      {messages.length === 0 && (
        <p className="text-center text-sm py-10" style={{ color: COLORS.mutedText }}>
          لا توجد رسائل بعد
        </p>
      )}
      {messages.map((m) => (
        <div key={m.id} className="rounded-2xl p-4" style={{ backgroundColor: COLORS.card }}>
          <div className="flex justify-between items-center mb-2">
            <p className="font-bold" style={{ color: COLORS.textDark }}>
              {m.guestName}
            </p>
            <p className="text-xs" style={{ color: COLORS.mutedText }}>
              {m.date}
            </p>
          </div>
          <p className="text-sm leading-6" style={{ color: COLORS.textDark }}>
            {m.text}
          </p>
        </div>
      ))}
    </div>
  );
}

function PrintAllCardsOverlay({ cards, onDone }) {
  const [images, setImages] = useState(null);

  useEffect(() => {
    const canvas = document.createElement("canvas");
    const rendered = cards.map((g, i) => {
      drawExtraCardToCanvas(canvas, g, i + 1);
      return canvas.toDataURL("image/png");
    });
    setImages(rendered);
  }, [cards]);

  useEffect(() => {
    if (!images) return;
    function handleAfterPrint() {
      onDone();
    }
    window.addEventListener("afterprint", handleAfterPrint);
    const t = setTimeout(() => window.print(), 250);
    return () => {
      clearTimeout(t);
      window.removeEventListener("afterprint", handleAfterPrint);
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [images]);

  return (
    <div className="fixed inset-0 z-[70] bg-black/60 flex flex-col">
      <style>{`
        @media print {
          @page { margin: 0.2in; }
          body * { visibility: hidden; }
          #print-all-cards, #print-all-cards * { visibility: visible; }
          #print-all-cards {
            position: fixed;
            inset: 0;
            display: flex !important;
            flex-wrap: wrap;
            gap: 0.15in;
            background: #fff !important;
          }
          #print-all-cards img {
            width: 3.5in;
            height: 2in;
            break-inside: avoid;
            page-break-inside: avoid;
            display: block;
          }
        }
      `}</style>
      <div className="m-auto rounded-2xl p-6 text-center" style={{ backgroundColor: COLORS.card, maxWidth: 320 }}>
        <Printer size={40} className="mx-auto" color={COLORS.oliveDark} />
        <p className="font-bold mt-3" style={{ color: COLORS.textDark }}>
          {images ? "جاري فتح نافذة الطباعة..." : `جاري تجهيز ${cards.length} كرت...`}
        </p>
        <p className="text-xs mt-2" style={{ color: COLORS.mutedText }}>
          سيتم طباعة كل الكروت بحجم كرت البزنس (3.5 × 2 إنش) بأمر طباعة واحد
        </p>
        <div className="mt-5">
          <SecondaryButton onClick={onDone}>إلغاء</SecondaryButton>
        </div>
      </div>
      <div id="print-all-cards" className="hidden">
        {images && images.map((src, i) => <img key={i} src={src} alt={`card-${i + 1}`} />)}
      </div>
    </div>
  );
}

function ExtraCardsTab({ guests, setGuests }) {
  const extraCards = guests.filter((g) => g.isExtraCard);
  const [previewUrl, setPreviewUrl] = useState(null);
  const [printAllOpen, setPrintAllOpen] = useState(false);
  const assignedCount = extraCards.filter((g) => g.name.trim()).length;

  function updateCard(id, patch) {
    setGuests((prev) => prev.map((g) => (g.id === id ? { ...g, ...patch } : g)));
  }

  function downloadCard(guest, cardNumber) {
    const canvas = document.createElement("canvas");
    drawExtraCardToCanvas(canvas, guest, cardNumber);
    setPreviewUrl(canvas.toDataURL("image/png"));
    updateCard(guest.id, { issued: true });
  }

  function handlePrintAllDone() {
    setPrintAllOpen(false);
    setGuests((prev) => prev.map((g) => (g.isExtraCard ? { ...g, issued: true } : g)));
  }

  const issuedCount = extraCards.filter((g) => g.issued).length;

  return (
    <div>
      <button
        onClick={() => setPrintAllOpen(true)}
        className="w-full rounded-2xl py-3.5 mb-4 flex items-center justify-center gap-2 font-bold text-white"
        style={{ backgroundColor: COLORS.oliveDark }}
      >
        <Printer size={18} />
        طباعة جميع الكروت ({extraCards.length}) بحجم كرت البزنس
      </button>

      <div className="rounded-2xl p-4 mb-4 text-sm leading-6" style={{ backgroundColor: COLORS.card, color: COLORS.mutedText }}>
        بطاقات جاهزة مسبقاً للضيوف الذين لا يملكون رقم جوال مسجّل — عبّئ الاسم والبيانات عند التسليم ثم نزّل البطاقة للطباعة.{" "}
        <span className="font-bold" style={{ color: COLORS.textDark }}>
          {assignedCount} / {extraCards.length}
        </span>{" "}
        تم تخصيصها ·{" "}
        <span className="font-bold" style={{ color: COLORS.orange }}>
          {issuedCount} / {extraCards.length}
        </span>{" "}
        تم تسليمها
        <span className="inline-flex items-center gap-1.5 mr-3">
          <span className="inline-block rounded" style={{ width: 10, height: 10, backgroundColor: COLORS.orangeTint, border: `1px solid ${COLORS.orange}` }} />
          يعني: تم تحميل الكود وإرساله لشخص
        </span>
      </div>

      <div className="rounded-2xl overflow-hidden" style={{ backgroundColor: COLORS.card }}>
        <div className="overflow-x-auto">
          <table className="w-full text-sm">
            <thead>
              <tr style={{ backgroundColor: COLORS.mutedGold }}>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  #
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  رمز الكود
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  اسم الضيف
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  الجوال
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  المرافقين البالغين
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  الأطفال
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  إجراء الجوال
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}>
                  دخول
                </th>
                <th className="px-3 py-2.5 text-right font-bold" style={{ color: COLORS.textDark }}></th>
              </tr>
            </thead>
            <tbody>
              {extraCards.map((g, index) => (
                <tr
                  key={g.id}
                  className="border-t"
                  style={{ borderColor: COLORS.mutedGold, backgroundColor: g.issued ? COLORS.orangeTint : "transparent" }}
                >
                  <td className="px-3 py-2.5 font-bold" style={{ color: COLORS.mutedText }}>
                    {index + 1}
                  </td>
                  <td className="px-3 py-2.5 font-bold whitespace-nowrap tracking-wider" style={{ color: COLORS.textDark }} dir="ltr">
                    {g.passCode}
                  </td>
                  <td className="px-3 py-2.5">
                    <input
                      value={g.name}
                      onChange={(e) => updateCard(g.id, { name: e.target.value })}
                      placeholder="اسم الضيف"
                      className="w-32 rounded-lg px-2 py-1.5 outline-none border"
                      style={{ backgroundColor: COLORS.cream, borderColor: COLORS.mutedGold, color: COLORS.textDark }}
                    />
                  </td>
                  <td className="px-3 py-2.5">
                    <input
                      value={g.phone}
                      onChange={(e) => updateCard(g.id, { phone: e.target.value })}
                      placeholder="05xxxxxxxx"
                      dir="ltr"
                      className="w-28 rounded-lg px-2 py-1.5 outline-none border"
                      style={{ backgroundColor: COLORS.cream, borderColor: COLORS.mutedGold, color: COLORS.textDark }}
                    />
                  </td>
                  <td className="px-3 py-2.5">
                    <input
                      type="number"
                      min={0}
                      value={g.companions}
                      onChange={(e) => updateCard(g.id, { companions: Number(e.target.value) || 0 })}
                      className="w-16 rounded-lg px-2 py-1.5 outline-none border text-center"
                      style={{ backgroundColor: COLORS.cream, borderColor: COLORS.mutedGold, color: COLORS.textDark }}
                    />
                  </td>
                  <td className="px-3 py-2.5">
                    <input
                      type="number"
                      min={0}
                      value={g.children}
                      onChange={(e) => updateCard(g.id, { children: Number(e.target.value) || 0 })}
                      className="w-16 rounded-lg px-2 py-1.5 outline-none border text-center"
                      style={{ backgroundColor: COLORS.cream, borderColor: COLORS.mutedGold, color: COLORS.textDark }}
                    />
                  </td>
                  <td className="px-3 py-2.5">
                    <select
                      value={g.phonePolicy || ""}
                      onChange={(e) => updateCard(g.id, { phonePolicy: e.target.value || null })}
                      className="w-32 rounded-lg px-2 py-1.5 outline-none border text-xs"
                      style={{
                        backgroundColor: COLORS.cream,
                        borderColor: g.phonePolicy ? PHONE_POLICIES[g.phonePolicy].color : COLORS.mutedGold,
                        color: COLORS.textDark,
                      }}
                    >
                      <option value="">بدون تحديد</option>
                      {Object.entries(PHONE_POLICIES).map(([key, p]) => (
                        <option key={key} value={key}>
                          {p.label}
                        </option>
                      ))}
                    </select>
                  </td>
                  <td className="px-3 py-2.5">
                    <button
                      onClick={() => updateCard(g.id, { checkedIn: !g.checkedIn })}
                      className="rounded-lg px-2.5 py-1.5 text-xs font-bold whitespace-nowrap"
                      style={{
                        backgroundColor: g.checkedIn ? COLORS.olive : COLORS.mutedGold,
                        color: g.checkedIn ? "#fff" : COLORS.textDark,
                      }}
                    >
                      {g.checkedIn ? "تم الدخول" : "تأكيد الدخول"}
                    </button>
                  </td>
                  <td className="px-3 py-2.5">
                    <div className="flex flex-col items-center gap-0.5">
                      <button
                        onClick={() => downloadCard(g, index + 1)}
                        className="p-1.5 rounded-lg"
                        style={{ color: g.issued ? COLORS.orange : COLORS.olive }}
                        title="تنزيل البطاقة"
                      >
                        <Download size={15} />
                      </button>
                      {g.issued && (
                        <span className="text-[10px] font-bold whitespace-nowrap" style={{ color: COLORS.orange }}>
                          تم الإرسال
                        </span>
                      )}
                    </div>
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>

      {previewUrl && <ImagePreviewModal dataUrl={previewUrl} onClose={() => setPreviewUrl(null)} />}
      {printAllOpen && <PrintAllCardsOverlay cards={extraCards} onDone={handlePrintAllDone} />}
    </div>
  );
}

function AdminDashboard({ guests, setGuests, messages, onExit }) {
  const [tab, setTab] = useState("guests");
  const tabs = [
    { id: "guests", label: "قائمة الضيوف", icon: Users },
    { id: "cards", label: "كروت إضافية", icon: CreditCard },
    { id: "messages", label: "رسائل الضيوف", icon: MessageSquare },
  ];

  return (
    <div className="min-h-screen" style={{ backgroundColor: COLORS.cream }}>
      <div className="px-5 py-5 max-w-4xl mx-auto">
        <div className="flex items-center justify-between mb-5">
          <h1 className="font-amiri text-2xl font-bold" style={{ color: COLORS.textDark }}>
            لوحة التحكم
          </h1>
          <button
            onClick={onExit}
            className="rounded-full px-4 py-2 text-xs font-bold"
            style={{ backgroundColor: COLORS.oliveDark, color: COLORS.cream }}
          >
            العودة للدعوة
          </button>
        </div>

        <div className="flex gap-2 mb-5 overflow-x-auto">
          {tabs.map((t) => {
            const Icon = t.icon;
            const active = tab === t.id;
            return (
              <button
                key={t.id}
                onClick={() => setTab(t.id)}
                className="flex items-center gap-1.5 rounded-xl px-4 py-2.5 text-sm font-bold whitespace-nowrap transition"
                style={{
                  backgroundColor: active ? COLORS.olive : COLORS.card,
                  color: active ? "#fff" : COLORS.textDark,
                }}
              >
                <Icon size={15} />
                {t.label}
              </button>
            );
          })}
        </div>

        {tab === "guests" && <GuestListTab guests={guests} setGuests={setGuests} />}
        {tab === "cards" && <ExtraCardsTab guests={guests} setGuests={setGuests} />}
        {tab === "messages" && <MessagesTab messages={messages} />}
      </div>
    </div>
  );
}

/* ---------- root ---------- */

export default function WeddingApp() {
  const [screen, setScreen] = useState("landing"); // landing|phone|notfound|rsvp|pass|declined
  const [currentGuestId, setCurrentGuestId] = useState(null);
  const [guests, setGuests] = useState(initialGuests);
  const [messages, setMessages] = useState(initialMessages);
  const [thankYouOpen, setThankYouOpen] = useState(false);
  const [adminUnlocked, setAdminUnlocked] = useState(false);
  const [scanUnlocked, setScanUnlocked] = useState(false);
  const [hash, setHash] = useState(typeof window !== "undefined" ? window.location.hash : "");

  useEffect(() => {
    function onHashChange() {
      setHash(window.location.hash);
    }
    window.addEventListener("hashchange", onHashChange);
    return () => window.removeEventListener("hashchange", onHashChange);
  }, []);

  const isAdminRoute = hash === "#/admin";
  const isScanRoute = hash === "#/scan";
  const currentGuest = guests.find((g) => g.id === currentGuestId) || null;

  function goAdmin() {
    window.location.hash = "#/admin";
  }
  function goScan() {
    window.location.hash = "#/scan";
  }
  function exitAdminToInvitation() {
    setAdminUnlocked(false);
    setScreen("landing");
    setCurrentGuestId(null);
    window.location.hash = "";
  }
  function exitScanToInvitation() {
    setScanUnlocked(false);
    setScreen("landing");
    setCurrentGuestId(null);
    window.location.hash = "";
  }

  function handleFoundGuest(guest) {
    setCurrentGuestId(guest.id);
    if (guest.status === "confirmed") setScreen("pass");
    else if (guest.status === "declined") setScreen("declined");
    else setScreen("rsvp");
  }

  function handleDecide(choice) {
    const status = choice === "confirm" ? "confirmed" : "declined";
    setGuests((prev) => prev.map((g) => (g.id === currentGuestId ? { ...g, status } : g)));
    setScreen(status === "confirmed" ? "pass" : "declined");
  }

  function handleSendThankYou(text) {
    setMessages((prev) => [
      { id: prev.length ? Math.max(...prev.map((m) => m.id)) + 1 : 1, guestName: currentGuest?.name || "ضيف", date: todayLabel(), text },
      ...prev,
    ]);
  }

  if (isAdminRoute) {
    if (!adminUnlocked) {
      return <AdminLockScreen onUnlock={() => setAdminUnlocked(true)} onBack={exitAdminToInvitation} />;
    }
    return <AdminDashboard guests={guests} setGuests={setGuests} messages={messages} onExit={exitAdminToInvitation} />;
  }

  if (isScanRoute) {
    if (!scanUnlocked) {
      return <ScanLockScreen onUnlock={() => setScanUnlocked(true)} onBack={exitScanToInvitation} />;
    }
    return <ScanPage guests={guests} setGuests={setGuests} onExit={exitScanToInvitation} />;
  }

  let body = null;
  if (screen === "landing") body = <LandingScreen onConfirm={() => setScreen("phone")} />;
  else if (screen === "phone")
    body = (
      <PhoneScreen
        guests={guests}
        onBack={() => setScreen("landing")}
        onFound={handleFoundGuest}
        onNotFound={() => setScreen("notfound")}
      />
    );
  else if (screen === "notfound") body = <NotFoundScreen onRetry={() => setScreen("phone")} />;
  else if (screen === "rsvp" && currentGuest)
    body = <RSVPScreen guest={currentGuest} onBack={() => setScreen("phone")} onDecide={handleDecide} />;
  else if (screen === "pass" && currentGuest)
    body = <PassScreen guest={currentGuest} onOpenThankYou={() => setThankYouOpen(true)} />;
  else if (screen === "declined") body = <DeclinedScreen onBackToInvite={() => setScreen("landing")} />;
  else body = <LandingScreen onConfirm={() => setScreen("phone")} />;

  return (
    <div dir="rtl">
      {body}
      <CornerControls onAdmin={goAdmin} onScan={goScan} />
      {thankYouOpen && currentGuest && (
        <ThankYouModal guest={currentGuest} onClose={() => setThankYouOpen(false)} onSend={handleSendThankYou} />
      )}
    </div>
  );
}
