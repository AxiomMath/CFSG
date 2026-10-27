module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.BabyMonster.Twin
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinGen
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinCensus
public import CFSG.Certificates.Kernel.BabyMonster.TwinCensus

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta def matRows (what : String) (n : Nat) (v : Val) : Except String (Array Nat) := do
  match v with
  | .list xs =>
    match xs[0]? with
    | some (.list _) =>
      let R ← flat what v
      unless R.size == n do throw s!"{what}: {R.size} rows"
      return R
    | _ => return rowsOfStrips n (← strips what n v)
  | _ => throw s!"{what}: not a list"

public meta def matStrips (what : String) (n : Nat) (v : Val) : Except String (Array Nat) := do
  match v with
  | .list xs =>
    match xs[0]? with
    | some (.list _) => return stripsOfRows n (← matRows what n v)
    | _ => strips what n v
  | _ => throw s!"{what}: not a list"

public meta def natArgs (args : Array Val) (i : Nat) : Except String (Array Nat) :=
  (args.extract i args.size).mapM fun
    | .nat x => pure x
    | _ => throw "expected a number"

public meta def rankCert (n : Nat) (M : Array Nat) : Option (Array Nat) := Id.run do
  let mut m := M
  let mut p : Array Nat := (Array.range n).map (1 <<< ·)
  let mut r := 0
  for c in [0:n] do
    let col := n - 1 - c
    let mut piv := r
    while piv < n && !m[piv]!.testBit col do
      piv := piv + 1
    if piv < n then
      let mr := m[piv]!
      let pr := p[piv]!
      m := (m.set! piv m[r]!).set! r mr
      p := (p.set! piv p[r]!).set! r pr
      for i in [r + 1:n] do
        if m[i]!.testBit col then
          m := m.modify i (· ^^^ mr)
          p := p.modify i (· ^^^ pr)
      r := r + 1
  let mut q := r
  for c in [0:n] do
    let col := n - 1 - c
    if q < n then
      let mut piv := q
      while piv < n && !p[piv]!.testBit col do
        piv := piv + 1
      if piv < n then
        let pq := p[piv]!
        p := (p.set! piv p[q]!).set! q pq
        for i in [q + 1:n] do
          if p[i]!.testBit col then
            p := p.modify i (· ^^^ pq)
        q := q + 1
  if q != n then return none
  return some p

public meta def powers (n d : Nat) (X : Array Nat) : Array (Array Nat) := Id.run do
  let I := stripsOfRows n ((Array.range n).map (1 <<< ·))
  let mut out := #[I]
  for i in [1:d + 1] do
    out := out.push (if i == 1 then X else mulStrips n out[i - 1]! X)
  return out

public meta def rank (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let some x := args[3]? | throw "no matrix"
  let cs ← natArgs args 4
  let d := cs.size - 1
  let mut M : Array Nat := Array.replicate n 0
  if d ≤ 1 then
    let X ← matRows "X" n x
    for i in [0:n] do
      let a := if cs[0]! % 2 == 1 then 1 <<< i else 0
      let b := if d == 1 && cs[1]! % 2 == 1 then X[i]! else 0
      M := M.set! i (a ^^^ b)
  else
    let Ps := powers n d (← matStrips "X" n x)
    for e in [0:d + 1] do
      if cs[e]! % 2 == 1 then
        let R := rowsOfStrips n Ps[e]!
        M := (Array.range n).map fun i => M[i]! ^^^ R[i]!
  let some P := rankCert n M | throw "the kernel rows of P are dependent"
  outStrips n size hash (stripsOfRows n P)

public meta def polyMul (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let (some p, some x) := (args[3]?, args[4]?) | throw "expected P and X"
  let P ← matStrips "P" n p
  let X ← matStrips "X" n x
  let cs ← natArgs args 5
  let mut acc : Array Nat := Array.replicate P.size 0
  let mut cur := P
  for e in [0:cs.size] do
    if e > 0 then cur := mulStrips n cur X
    if cs[e]! % 2 == 1 then acc := (Array.range P.size).map fun s => acc[s]! ^^^ cur[s]!
  outStrips n size hash acc

public meta def xorRows (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (some (Val.nat size), some (Val.nat hash)) := (args[0]?, args[1]?) | throw "xorRows: no pin"
  let Rs ← (args.extract 2 args.size).mapM (flat "R")
  let some R0 := Rs[0]? | throw "xorRows: no matrix"
  let mut acc := R0
  for R in Rs.extract 1 Rs.size do
    unless R.size == acc.size do throw s!"xorRows: {R.size} rows, expected {acc.size}"
    acc := (Array.range acc.size).map fun i => acc[i]! ^^^ R[i]!
  outRows size hash acc

public meta def xorStrips (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let As ← (args.extract 3 args.size).mapM (strips "A" n)
  let some A0 := As[0]? | throw "xorStrips: no matrix"
  let mut acc := A0
  for A in As.extract 1 As.size do
    acc := (Array.range acc.size).map fun s => acc[s]! ^^^ A[s]!
  outStrips n size hash acc

public meta def mtInit (seed : UInt32) : Array UInt32 := Id.run do
  let mut mt : Array UInt32 := Array.replicate 624 0
  mt := mt.set! 0 19650218
  for i in [1:624] do
    let x := mt[i - 1]!
    mt := mt.set! i ((1812433253 : UInt32) * (x ^^^ (x >>> 30)) + i.toUInt32)
  let mut i := 1
  for _ in [0:624] do
    let x := mt[i - 1]!
    mt := mt.set! i ((mt[i]! ^^^ ((x ^^^ (x >>> 30)) * 1664525)) + seed)
    i := i + 1
    if i ≥ 624 then
      mt := mt.set! 0 mt[623]!
      i := 1
  for _ in [0:623] do
    let x := mt[i - 1]!
    mt := mt.set! i ((mt[i]! ^^^ ((x ^^^ (x >>> 30)) * 1566083941)) - i.toUInt32)
    i := i + 1
    if i ≥ 624 then
      mt := mt.set! 0 mt[623]!
      i := 1
  mt := mt.set! 0 0x80000000
  return mt

public meta def mtTwist (mt : Array UInt32) : Array UInt32 := Id.run do
  let mut mt := mt
  for k in [0:624] do
    let y := (mt[k]! &&& 0x80000000) ||| (mt[(k + 1) % 624]! &&& 0x7fffffff)
    let v := mt[(k + 397) % 624]! ^^^ (y >>> 1) ^^^ (if y &&& 1 == 1 then 0x9908b0df else 0)
    mt := mt.set! k v
  return mt

public meta def mtTemper (y : UInt32) : UInt32 :=
  let y := y ^^^ (y >>> 11)
  let y := y ^^^ ((y <<< 7) &&& 0x9d2c5680)
  let y := y ^^^ ((y <<< 15) &&& 0xefc60000)
  y ^^^ (y >>> 18)

public meta def mtRows (seed n rows : Nat) : Array Nat := Id.run do
  let mut mt := mtInit seed.toUInt32
  let mut idx := 624
  let words := (n - 1) / 32 + 1
  let mut out : Array Nat := Array.mkEmpty rows
  for _ in [0:rows] do
    let mut ws : Array UInt64 := Array.replicate ((words + 1) / 2) 0
    let mut k := n
    for w in [0:words] do
      if idx ≥ 624 then
        mt := mtTwist mt
        idx := 0
      let mut r := mtTemper mt[idx]!
      idx := idx + 1
      if k < 32 then r := r >>> (32 - k).toUInt32
      ws := ws.modify (w / 2) (· ||| (r.toUInt64 <<< (32 * (w % 2)).toUInt64))
      k := k - 32
    out := out.push (natOfWords ws 0 ws.size)
  return out

public meta def mtStrips (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[.nat n, .nat seed, .nat size, .nat hash] := args | throw "mtStrips: arguments"
  unless 4352 < n && n ≤ 4416 && seed < 2 ^ 32 do throw s!"mtStrips: dimension {n}, seed {seed}"
  outStrips n size hash (stripsOfRows n (mtRows seed n n))

public meta def compact8 (x : Nat) : Nat := Id.run do
  let mut x := x
  let mut g := 1
  while g ≤ 4096 do
    let K := rep ((1 <<< g) - 1) (16 * g) (65536 / (16 * g) + 1)
    x := (x &&& K) ||| ((x >>> (7 * g)) &&& (K <<< g))
    g := 2 * g
  return x

public meta def textRows (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[.nat size, .nat hash, t] := args | throw "textRows: arguments"
  let T ← nats "T" t
  let n := 4370
  unless T.size == 69 do throw s!"textRows: {T.size} blocks"
  let digit0 := rep 48 8 n
  let low := rep 254 8 n
  let mut R : Array Nat := Array.mkEmpty n
  for s in [0:69] do
    let m := min 64 (n - 64 * s)
    unless T[s]! >>> (35400 * m) == 0 do throw s!"block {s}: more than {m} rows"
    for t in [0:m] do
      let r := (T[s]! >>> (35400 * t)) &&& ((1 <<< 35400) - 1)
      let mut x := 0
      for l in [0:55] do
        let len := if l < 54 then 80 else 50
        unless (r >>> (8 * (81 * l + len))) &&& 255 == 10 do
          throw s!"row {64 * s + t}: line {l} not ended by a newline"
        x := x ||| (((r >>> (648 * l)) &&& ((1 <<< (8 * len)) - 1)) <<< (640 * l))
      let y := x ^^^ digit0
      unless y &&& low == 0 do throw s!"row {64 * s + t}: a byte is not a digit 0 or 1"
      R := R.push (compact8 y)
  outRows size hash R

public meta def b64Decode (t : ByteArray) : ByteArray := Id.run do
  let mut raw : ByteArray := ByteArray.emptyWithCapacity (t.size * 3 / 4)
  let mut acc := 0
  let mut nb := 0
  for i in [0:t.size] do
    let v := b64 t[i]!
    if v < 64 then
      acc := (acc <<< 6) ||| v
      nb := nb + 6
      if nb ≥ 8 then
        nb := nb - 8
        raw := raw.push ((acc >>> nb) &&& 255).toUInt8
        acc := acc &&& ((1 <<< nb) - 1)
  return raw

public meta def b64Rows (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[.nat n, .nat k, .nat size, .nat hash, .nat t] := args | throw "b64Rows: arguments"
  let b := b64Decode (minBytes t)
  unless b.size == size && b.hash.toNat == hash do
    throw s!"decoded file of size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"
  let u32 (o : Nat) : Nat := natOfBytes b o (o + 4)
  let cnt := u32 8
  unless u32 0 == 1 && u32 4 == n && u32 12 == 69 && b.size == 16 + cnt * n * 552 && k < cnt do
    throw s!"headed file: header ({u32 0}, {u32 4}, {cnt}, {u32 12}), size {b.size}"
  let base := 16 + k * n * 552
  let R := (Array.range n).map fun i => natOfBytes b (base + 552 * i) (base + 552 * (i + 1))
  for i in [0:n] do
    unless R[i]! >>> n == 0 do throw s!"row {i} has a bit past column {n}"
  outRows 0 0 R

end CFSG.KC.BM.Twin
