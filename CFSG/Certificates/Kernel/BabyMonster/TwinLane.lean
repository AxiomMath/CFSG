module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinGen
public import CFSG.Certificates.Kernel.BabyMonster.TwinGen

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta def laneSpread (x : Nat) : Nat := Id.run do
  let mut out := 0
  let mut y := x
  let mut k := 0
  while y != 0 do
    out := out ||| ((y &&& 65535) <<< (256 * k))
    y := y >>> 16
    k := k + 1
  return out

public meta def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

public meta def laneRecs (B : Array Nat) : Array (Array Nat) := Id.run do
  let mut recs : Array (Array Nat) := #[]
  for s in [0:274] do
    let r := min 16 (4371 - 16 * s)
    let mut S := 0
    let mut ps : Array Nat := #[]
    for t in [0:r] do
      let b := B[16 * s + t]!
      S := S ||| (laneSpread b <<< (272 * t))
      ps := ps.push (b &&& 65535)
    let mut st : UInt64 := (0x9E3779B97F4A7C15 : UInt64) ^^^ (s + 1).toUInt64
    let mut salt := 0
    for i in [0:4] do
      st := xorshift (xorshift st)
      salt := salt ||| (st.toNat <<< (64 * i))
    S := S ||| (salt &&& (((1 <<< 256) - 1) ^^^ 65535))
    recs := recs.push (#[S] ++ ps)
  return recs

public meta def lanePin (recs : Array (Array Nat)) : Nat × Nat :=
  let b := natsBytes (recs.foldl (· ++ ·) #[])
  (b.size, b.hash.toNat)

public meta def laneStrips (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[Val.nat size, Val.nat hash, bs] := args | throw "laneStrips: arguments"
  let B ← flat "Bs" bs
  unless B.size == 4371 do throw s!"{B.size} basis rows"
  let recs := laneRecs B
  if size != 0 then
    let (sz, h) := lanePin recs
    unless sz == size && h == hash do
      throw s!"result of size {sz} hash {h}, pinned size {size} hash {hash}"
  let names := (Array.range 274).map fun s => Lean.Name.mkSimple s!"t{s}"
  let vals := recs.map fun r => Val.list (r.map .nat)
  return (names.zip vals).push (.anonymous, .list (names.map .ref))

public meta def dyCont (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[Val.nat size, Val.nat hash, bs] := args | throw "dyCont: arguments"
  let B ← flat "Bs" bs
  let M := rep 127 16 4371
  let mut R := Array.mkEmpty B.size
  for i in [0:B.size] do
    let b := B[i]!
    let v := (((128 / (b &&& 65535)) * b) &&& M) >>> 16
    let some r := dyElim 128 B (v <<< (16 * (i + 1))) | throw s!"row {i}: elimination fails"
    R := R.push r
  outRows size hash R

public meta def laneKs (w W : Nat) : Array Nat :=
  (Array.range 13).reverse.map fun b => rep ((1 <<< (w * 2 ^ b)) - 1) (W * 2 ^ (b + 1)) (2 ^ (12 - b))

public meta def laneMasks (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[Val.nat size, Val.nat hash] := args | throw "laneMasks: arguments"
  let ks := #[(1, 16), (16, 32), (32, 64), (64, 128), (128, 256)].map fun (w, W) => laneKs w W
  if size != 0 then
    let b := natsBytes (ks.foldl (· ++ ·) #[])
    unless b.size == size && b.hash.toNat == hash do
      throw s!"result of size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"
  let names := (Array.range 5).map fun i => Lean.Name.mkSimple s!"K{i}"
  return (names.zip (ks.map fun k => Val.list (k.map .nat))).push (.anonymous, .list (names.map .ref))

end CFSG.KC.BM.Twin
