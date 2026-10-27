module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.BabyMonster.Twin
public meta import CFSG.Certificates.Kernel.Common.HarnessGz
public meta import CFSG.Certificates.Kernel.Common.Repo
meta import all CFSG.Certificates.Kernel.Common.Eval
meta import all CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.Twin
public import CFSG.Certificates.Kernel.Common.HarnessGz
public import CFSG.Certificates.Kernel.Common.Repo

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta def rep (x p c : Nat) : Nat := x * (((1 <<< (p * c)) - 1) / ((1 <<< p) - 1))

public meta def benesDs : Array Nat :=
  #[65536, 32768, 16384, 8192, 4096, 2048, 1024, 512, 256, 128, 64, 32, 16, 32, 64, 128, 256, 512,
    1024, 2048, 4096, 8192, 16384, 32768, 65536]

public meta def benes (Ms : Array Nat) (x : Nat) : Nat := Id.run do
  let mut x := x
  for i in [0:min Ms.size benesDs.size] do
    let D := benesDs[i]!
    let t := ((x >>> D) ^^^ x) &&& Ms[i]!
    x := x ^^^ (t ^^^ (t <<< D))
  return x

public meta def dyElim (m : Nat) (B : Array Nat) (v : Nat) : Option Nat := Id.run do
  let M := rep (m - 1) 16 4371
  let mut v := v
  let mut out := 0
  for j in [0:B.size] do
    let x := v &&& 65535
    if x == 0 then
      v := v >>> 16
    else
      let b := B[j]!
      let p := b &&& 65535
      if x % p != 0 then return none
      let q := x / p
      out := out ||| ((q &&& 1) <<< j)
      v := ((v + (m - q) * b) &&& M) >>> 16
  if v != 0 then return none
  return some out

public meta def monoImg (Ms : Array Nat) (NM i b : Nat) : Nat :=
  let v := benes Ms (b <<< (16 * i))
  let w := v &&& NM
  v - w + (((NM &&& rep 256 16 4371) - w) &&& rep 255 16 4371)

public meta def colorImg (Cs : Array (Array Nat)) (x : Nat) : Option Nat := Id.run do
  let one := rep 1 16 4371
  let mut acc := 0
  for C in Cs do
    let y := 2 * (x &&& C[0]!) + 4 * (x &&& C[1]!) + 8 * (x &&& C[2]!) +
      ((2048 * (C[3]! &&& one) - 2 * (x &&& C[3]!)) + (2048 * (C[4]! &&& one) - 4 * (x &&& C[4]!)) +
        (2048 * (C[5]! &&& one) - 8 * (x &&& C[5]!)))
    acc := acc + benes (C.extract 6 C.size) y
  let w := acc &&& rep 2047 16 4371
  if w &&& rep 7 16 4371 != 0 then return none
  return some (w >>> 3)

public meta def nats (what : String) (v : Val) : Except String (Array Nat) := do
  let .list xs := v | throw s!"{what}: not a list"
  xs.mapM fun
    | .nat x => pure x
    | _ => throw s!"{what}: an entry is not a number"

public meta def flat (what : String) (v : Val) : Except String (Array Nat) := do
  let .list xs := v | throw s!"{what}: not a list"
  let mut out := #[]
  for x in xs do
    out := out ++ (← nats what x)
  return out

public meta def firstBlock (what : String) (v : Val) : Except String (Array Nat) := do
  let .list xs := v | throw s!"{what}: not a list"
  let some x := xs[0]? | throw s!"{what}: empty"
  nats what x

public meta def projRow (p f r : Nat) : Nat :=
  let y := r ^^^ (((r >>> p) &&& 1) * f)
  (y &&& ((1 <<< p) - 1)) ||| ((y >>> (p + 1)) <<< p)

public meta def rowBytes (R : Array Nat) : ByteArray := Id.run do
  let mut b : ByteArray := ByteArray.emptyWithCapacity (R.size * 552)
  for x in R do
    for w in natWords x 69 do
      for i in [0:8] do
        b := b.push (w >>> (8 * i).toUInt64).toUInt8
  return b

public meta def outRows (size hash : Nat) (R : Array Nat) : Except String (Array (Lean.Name × Val)) := do
  if size != 0 then
    let b := rowBytes R
    unless b.size == size && b.hash.toNat == hash do
      throw s!"result of size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"
  let nb := (R.size + 63) / 64
  let names := (Array.range nb).map fun s => Lean.Name.mkSimple s!"rb{s}"
  let blocks := (Array.range nb).map fun s => Val.list ((R.extract (64 * s) (64 * s + 64)).map .nat)
  return (names.zip blocks).push (`rows, .list (names.map .ref))

public meta def quot (p f : Nat) (R : Array Nat) : Array Nat :=
  if p ≥ R.size then R
  else ((R.extract 0 p) ++ (R.extract (p + 1) R.size)).map (projRow p f)

public meta def dyMono (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[Val.nat size, Val.nat hash, Val.nat p, Val.nat f, bs, ms, gs] := args | throw "dyMono: arguments"
  let B ← flat "Bs" bs
  let Ms ← firstBlock "M" ms
  let some NM := (← firstBlock "G" gs)[1]? | throw "G: no negation mask"
  let mut R := Array.mkEmpty B.size
  for i in [0:B.size] do
    let some r := dyElim 256 B (monoImg Ms NM i B[i]!) | throw s!"row {i}: elimination fails"
    R := R.push r
  outRows size hash (quot p f R)

public meta def dyColor (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let some (Val.nat size) := args[0]? | throw "dyColor: no pin"
  let some (Val.nat hash) := args[1]? | throw "dyColor: no pin"
  let some bs := args[2]? | throw "dyColor: no basis"
  let B ← flat "Bs" bs
  let Cs ← (args.extract 3 args.size).mapM (firstBlock "C")
  let mut R := Array.mkEmpty B.size
  for i in [0:B.size] do
    let some x := colorImg Cs (B[i]! <<< (16 * i)) | throw s!"row {i}: colour image fails"
    let some r := dyElim 256 B x | throw s!"row {i}: elimination fails"
    R := R.push r
  outRows size hash R

public meta def quotRows (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[Val.nat p, Val.nat f, Val.nat size, Val.nat hash, c] := args | throw "quotRows: arguments"
  outRows size hash (quot p f (← flat "C" c))

public meta def stripsOf (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let some r := args[3]? | throw "no rows"
  let R ← flat "R" r
  unless R.size == n do throw s!"{R.size} rows"
  outStrips n size hash (stripsOfRows n R)

public meta def rowsOf (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let some s := args[3]? | throw "no matrix"
  outRows size hash (rowsOfStrips n (← strips "S" n s))

public meta partial def fields (x w k : Nat) : Array Nat :=
  if k == 0 then #[]
  else if k == 1 then #[x % (1 <<< w)]
  else
    let h := k / 2
    fields (x % (1 <<< (w * h))) w h ++ fields (x >>> (w * h)) w (k - h)

public meta def rowsBin (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let some (Val.nat x) := args[3]? | throw "rowsBin: no row file"
  let R := fields x 4416 n
  for i in [0:R.size] do
    unless R[i]! >>> n == 0 do throw s!"row {i} has a bit past column {n}"
  outRows size hash R
