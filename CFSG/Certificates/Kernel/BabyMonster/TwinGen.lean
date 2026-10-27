module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.BabyMonster.Twin
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
public import CFSG.Certificates.Kernel.BabyMonster.TwinDy

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta def minBytes (x : Nat) : ByteArray := Id.run do
  if x == 0 then return .empty
  let n := (x.log2 + 8) / 8
  let ws := natWords x ((n + 7) / 8)
  let mut b : ByteArray := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    b := b.push (ws[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8
  return b

public meta def setBitB (b : ByteArray) (p : Nat) : ByteArray :=
  b.set! (p >>> 3) (b.get! (p >>> 3) ||| ((1 : UInt8) <<< (p &&& 7).toUInt8))

public meta def route (m : Nat) (dst : Array Nat) : Array ByteArray := Id.run do
  let W := 1 <<< m
  let zero : ByteArray := ⟨Array.replicate ((W + 7) / 8) 0⟩
  let mut masks : Array ByteArray := Array.replicate (2 * m - 1) zero
  let mut f := dst
  let mut finv : Array Nat := Array.replicate W 0
  for q in [0:W] do
    finv := finv.set! f[q]! q
  for lvl in [0:m - 1] do
    let h := 1 <<< (m - 1 - lvl)
    let lowH := h - 1
    let hiMask := (W - 1) ^^^ (2 * h - 1)
    let mut col : ByteArray := ⟨Array.replicate W 2⟩
    for q0 in [0:W] do
      if col.get! q0 == 2 then
        let mut q := q0
        let mut go := true
        while go do
          col := col.set! q 0
          let q2 := finv[f[q]! ^^^ h]!
          col := col.set! q2 1
          let q3 := q2 ^^^ h
          if col.get! q3 == 2 then q := q3 else go := false
    let mut mi := masks[lvl]!
    let mut mo := masks[2 * m - 2 - lvl]!
    masks := masks.set! lvl zero
    masks := masks.set! (2 * m - 2 - lvl) zero
    let mut nf : Array Nat := Array.replicate W 0
    let mut nfi : Array Nat := Array.replicate W 0
    for q in [0:W] do
      let c := col.get! q
      if q &&& h == 0 then
        if c == 1 then mi := setBitB mi q
        if col.get! finv[q]! == 1 then mo := setBitB mo q
      let base := (q &&& hiMask) + (if c == 1 then h else 0)
      let p := base + (q &&& lowH)
      let d := base + (f[q]! &&& lowH)
      nf := nf.set! p d
      nfi := nfi.set! d p
    masks := masks.set! lvl mi
    masks := masks.set! (2 * m - 2 - lvl) mo
    f := nf
    finv := nfi
  let mut mid := masks[m - 1]!
  masks := masks.set! (m - 1) zero
  for p in [0:W / 2] do
    if f[2 * p]! != 2 * p then mid := setBitB mid (2 * p)
  masks := masks.set! (m - 1) mid
  return masks

public meta def natsBytes (R : Array Nat) : ByteArray := Id.run do
  let mut b : ByteArray := .empty
  for x in R do
    let bs := minBytes x
    let m := bs.size
    b := b.push m.toUInt8 |>.push (m >>> 8).toUInt8 |>.push (m >>> 16).toUInt8 |>.push (m >>> 24).toUInt8
    b := b ++ bs
  return b

public meta def outNats (pre : Lean.Name) (size hash : Nat) (R : Array Nat) :
    Except String (Array (Lean.Name × Val)) := do
  if size != 0 then
    let b := natsBytes R
    unless b.size == size && b.hash.toNat == hash do
      throw s!"result of size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"
  let nb := (R.size + 63) / 64
  let names := (Array.range nb).map fun s => pre ++ Lean.Name.mkSimple s!"b{s}"
  let blocks := (Array.range nb).map fun s => Val.list ((R.extract (64 * s) (64 * s + 64)).map .nat)
  return (names.zip blocks).push (pre, .list (names.map .ref))

public meta def b64 (c : UInt8) : Nat :=
  if 65 ≤ c && c ≤ 90 then (c - 65).toNat
  else if 97 ≤ c && c ≤ 122 then (c - 71).toNat
  else if 48 ≤ c && c ≤ 57 then (c + 4).toNat
  else if c == 43 then 62 else if c == 47 then 63 else 64

public meta def basisOf (t : ByteArray) : Except String (Array Nat) := do
  let n := 4371
  let mut ks : Array Nat := #[]
  let mut i := 0
  while i < t.size && t[i]! != 10 do
    ks := ks.push (t[i]! - 48).toNat
    i := i + 1
  unless ks.size == n do throw s!"line 1 has {ks.size} digits"
  i := i + 1
  let mut raw : ByteArray := .empty
  let mut acc := 0
  let mut nb := 0
  while i < t.size && t[i]! != 10 do
    let v := b64 t[i]!
    if v < 64 then
      acc := (acc <<< 6) ||| v
      nb := nb + 6
      if nb ≥ 8 then
        nb := nb - 8
        raw := raw.push ((acc >>> nb) &&& 255).toUInt8
        acc := acc &&& ((1 <<< nb) - 1)
    i := i + 1
  let mut R : Array Nat := Array.mkEmpty n
  let mut pos := 0
  for r in [0:n] do
    let mut ws : Array UInt64 := Array.replicate ((n - r + 3) / 4) 0
    ws := ws.set! 0 (1 <<< ks[r]!.toUInt64)
    for j in [r + 1:n] do
      let bit := 7 * pos
      let w := raw[bit / 8]!.toNat ||| (raw[bit / 8 + 1]?.getD 0).toNat <<< 8
      let e := (w >>> (bit % 8)) &&& 127
      let f := j - r
      ws := ws.modify (f / 4) (· ||| (e.toUInt64 <<< (16 * (f % 4)).toUInt64))
      pos := pos + 1
    R := R.push (natOfWords ws 0 ws.size)
  return R

public meta def latBasis (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[Val.nat size, Val.nat hash, Val.nat t] := args | throw "latBasis: arguments"
  outNats .anonymous size hash (← basisOf (minBytes t))

public meta def lineInts (t : ByteArray) (lo hi : Nat) : Array Int := Id.run do
  let mut out : Array Int := #[]
  let mut i := lo
  while i < hi do
    while i < hi && t[i]! == 32 do
      i := i + 1
    if i ≥ hi then break
    let neg := t[i]! == 45
    if neg then i := i + 1
    let mut v := 0
    while i < hi && t[i]! != 32 do
      v := 10 * v + (t[i]! - 48).toNat
      i := i + 1
    out := out.push (if neg then -(v : Int) else v)
  return out

public meta def ratGen (t : ByteArray) (g : Nat) : Except String (Int × Array (Array (Nat × Int))) := do
  let mut starts : Array Nat := #[0]
  for i in [0:t.size] do
    if t[i]! == 10 then starts := starts.push (i + 1)
  let line (k : Nat) : Array Int := lineInts t starts[k]! (starts[k + 1]! - 1)
  let hdr := line 0
  let some n := hdr[0]? | throw "no header"
  unless n == 4371 do throw s!"dimension {n}"
  let base := 1 + g * 4372
  unless base + 4372 < starts.size do throw s!"no generator {g}"
  let some d := (line base)[0]? | throw "no denominator"
  let mut rows := Array.mkEmpty 4371
  for j in [0:4371] do
    let f := line (base + 1 + j)
    let m := (f[0]?.getD 0).toNat
    unless f.size == 2 * m + 1 do throw s!"row {j}: {f.size} tokens"
    rows := rows.push ((Array.range m).map fun i => ((f[1 + 2 * i]!).toNat, f[2 + 2 * i]!))
  return (d, rows)

public meta def genArg (args : Array Val) : Except String (Nat × Nat × Int × Array (Array (Nat × Int))) := do
  match args[0]?, args[1]?, args[2]?, args[3]? with
  | some (Val.nat size), some (Val.nat hash), some (Val.nat g), some (Val.nat s) =>
    let (d, rows) ← ratGen (minBytes s) g
    return (size, hash, d, rows)
  | _, _, _, _ => throw "expected size, hash, generator, text"

public meta def monoOf (d : Int) (rows : Array (Array (Nat × Int))) : Except String (Array Nat × Array Bool) := do
  let mut σ := #[]
  let mut neg := #[]
  for r in rows do
    let #[(k, c)] := r | throw "not monomial"
    unless c == d || c == -d do throw s!"entry {c}"
    σ := σ.push k
    neg := neg.push (decide (c < 0))
  return (σ, neg)

public meta def ofFields (fs : Array Nat) : Nat := Id.run do
  let mut ws : Array UInt64 := Array.replicate ((fs.size + 3) / 4) 0
  for i in [0:fs.size] do
    ws := ws.modify (i / 4) (· ||| (fs[i]!.toUInt64 <<< (16 * (i % 4)).toUInt64))
  return natOfWords ws 0 ws.size

public meta def ratMono (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (size, hash, d, rows) ← genArg args
  let (σ, neg) ← monoOf d rows
  let T := ofFields ((Array.range 4371).map fun j => σ[j]! + if neg[j]! then 8192 else 0)
  let mut nm : Array Nat := Array.replicate 4371 0
  for j in [0:4371] do
    if neg[j]! then nm := nm.set! σ[j]! 65535
  outNats .anonymous size hash #[T, ofFields nm]

public meta def netMasks (dst : Array Nat) : Except String (Array Nat) := do
  let inv := Id.run do
    let mut a := Array.replicate 8192 0
    for j in [0:8192] do
      a := a.set! dst[j]! j
    return a
  let x0 := ofFields (Array.range 8192)
  let y := ofFields inv
  for d in #[dst, inv] do
    let Ms := (route 13 d).map fun mk => ofFields ((Array.range 8192).map fun q =>
      if (mk.get! (q / 8) >>> (q % 8).toUInt8) &&& 1 == 1 then 65535 else 0)
    if benes Ms x0 == y then return Ms
  throw "the routed network does not realize the permutation"

public meta def ratNet (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (size, hash, d, rows) ← genArg args
  let (σ, _) ← monoOf d rows
  outNats .anonymous size hash (← netMasks (σ ++ (Array.range' 4371 (8192 - 4371))))

public meta def ratSparse (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (size, hash, _, rows) ← genArg args
  outNats .anonymous size hash (rows.map fun r =>
    r.foldl (fun x (k, c) => x ||| ((c % 2048).toNat <<< (16 * k))) 0)

public meta def colourEdges (nc : Nat) (E : Array (Nat × Nat)) : Option (Array Nat) := Id.run do
  let n := 4371
  let none' := E.size
  let mut slot : Array Nat := Array.replicate (2 * n * nc) none'
  let mut col : Array Nat := Array.replicate E.size nc
  for e in [0:E.size] do
    let (j, k) := E[e]!
    let u := j
    let v := n + k
    let some a := (List.range nc).find? (fun c => slot[u * nc + c]! == none') | return none
    let some b := (List.range nc).find? (fun c => slot[v * nc + c]! == none') | return none
    if slot[v * nc + a]! != none' then
      let mut path : Array Nat := #[]
      let mut w := v
      let mut c := a
      while slot[w * nc + c]! != none' do
        let f := slot[w * nc + c]!
        path := path.push f
        let (fj, fk) := E[f]!
        w := if w == fj then n + fk else fj
        c := if c == a then b else a
      for f in path do
        let (fj, fk) := E[f]!
        slot := slot.set! (fj * nc + col[f]!) none'
        slot := slot.set! ((n + fk) * nc + col[f]!) none'
      for f in path do
        let (fj, fk) := E[f]!
        let c' := if col[f]! == a then b else a
        col := col.set! f c'
        slot := slot.set! (fj * nc + c') f
        slot := slot.set! ((n + fk) * nc + c') f
    col := col.set! e a
    slot := slot.set! (u * nc + a) e
    slot := slot.set! (v * nc + a) e
  return some col

public meta def ratColors (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let some (Val.nat g) := args[0]? | throw "ratColors: no generator"
  let some (Val.nat s) := args[1]? | throw "ratColors: no text"
  let (_, rows) ← ratGen (minBytes s) g
  let mut E : Array (Nat × Nat) := #[]
  let mut V : Array Int := #[]
  for j in [0:rows.size] do
    for (k, c) in rows[j]! do
      E := E.push (j, k)
      V := V.push c
  let some col := colourEdges 16 E | throw "a row or column has more than 16 entries"
  let mut out := #[]
  for t in [0:16] do
    let mut sel : Array (Array Nat) := Array.replicate 6 (Array.replicate 4371 0)
    let mut dst : Array Nat := Array.replicate 8192 8192
    let mut used : Array Bool := Array.replicate 8192 false
    for e in [0:E.size] do
      if col[e]! == t then
        let (j, k) := E[e]!
        let c := V[e]!
        let idx := (if c < 0 then 3 else 0) + (if c.natAbs == 2 then 0 else if c.natAbs == 4 then 1 else 2)
        unless c.natAbs == 2 || c.natAbs == 4 || c.natAbs == 8 do throw s!"entry {c}"
        sel := sel.modify idx (·.set! j 65535)
        dst := dst.set! j k
        used := used.set! k true
    let mut free := 0
    for q in [0:8192] do
      if dst[q]! == 8192 then
        while used[free]! do
          free := free + 1
        dst := dst.set! q free
        used := used.set! free true
    let Ms ← netMasks dst
    let pre := Lean.Name.mkSimple s!"CL{g}_{t}"
    let pin := fun k => match args[2 + 2 * t + k]? with | some (Val.nat v) => v | _ => 0
    out := out ++ (← outNats pre (pin 0) (pin 1) ((sel.map ofFields) ++ Ms))
  return out

end CFSG.KC.BM.Twin
