module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.BabyMonster.Twin
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
public import CFSG.Certificates.Kernel.BabyMonster.TwinRank

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta def stripRows (n A : Nat) : Array Nat := Id.run do
  let nb := (n + 63) / 64
  let ws := natWords A n
  let mut rw : Array (Array UInt64) := Array.replicate 64 (Array.replicate nb 0)
  for c in [0:nb] do
    let tb := transpose64 ((Array.range 64).map fun j => if 64 * c + j < n then ws[64 * c + j]! else 0)
    for t in [0:64] do
      rw := rw.modify t (·.set! c tb[t]!)
  return rw.map (natOfWords · 0 nb)

public meta def rowsStrip (n : Nat) (R : Array Nat) : Nat := Id.run do
  let nb := (n + 63) / 64
  let rw := (Array.range 64).map fun t =>
    if h : t < R.size then natWords R[t] nb else Array.replicate nb 0
  let mut ws : Array UInt64 := Array.replicate (64 * nb) 0
  for c in [0:nb] do
    let tb := transpose64 ((Array.range 64).map fun t => rw[t]![c]!)
    for j in [0:64] do
      ws := ws.set! (64 * c + j) tb[j]!
  return natOfWords ws 0 n

public meta def vecRows (n : Nat) (M : Array Nat) (v : Nat) : Nat := Id.run do
  let ws := natWords v ((n + 63) / 64)
  let mut acc := 0
  for c in [0:ws.size] do
    let w := ws[c]!
    if w != 0 then
      for b in [0:64] do
        if (w >>> b.toUInt64) &&& 1 == 1 then
          acc := acc ^^^ M[64 * c + b]?.getD 0
  return acc

public meta def mulRows (n : Nat) (M : Array Nat) (A : Nat) : Nat :=
  rowsStrip n ((stripRows n A).map (vecRows n M))

public meta def spreadVec (n v : Nat) : Nat :=
  let ws := natWords v ((n + 63) / 64)
  natOfWords ((Array.range n).map fun j => (ws[j / 64]! >>> (j % 64).toUInt64) &&& 1) 0 n

public meta def stripArg (what : String) : Val → Except String Nat
  | .nat x => pure x
  | .list xs => match xs[0]? with
    | some (Val.nat x) => pure x
    | _ => throw s!"{what}: not a strip or a list of strips"
  | _ => throw s!"{what}: not a strip"

public meta def outStrip (n size hash A : Nat) : Except String (Array (Lean.Name × Val)) := do
  if size != 0 then
    let b := stripBytes n #[A]
    unless b.size == size && b.hash.toNat == hash do
      throw s!"result of size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"
  return #[(.anonymous, .nat A)]

public meta def vword (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let some a := args[3]? | throw "vword: no strip"
  let mut A ← stripArg "A" a
  for i in [4:args.size] do
    A := mulRows n (← matRows s!"M{i - 3}" n args[i]!) A
  outStrip n size hash A

public meta def vrepl (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let (some s, some (Val.nat m0)) := (args[3]?, args[4]?) | throw "vrepl: expected S and m₀"
  unless args.size % 2 == 1 do throw "vrepl: a matrix without its mask"
  let S ← stripArg "S" s
  let sm := spreadMask n
  let mut acc := S - (S &&& (sm * m0))
  for k in [0:(args.size - 5) / 2] do
    let .nat m := args[6 + 2 * k]! | throw s!"vrepl: mask {k + 1} is not a number"
    let M ← matRows s!"M{k + 1}" n args[5 + 2 * k]!
    acc := acc ||| mulRows n M (S &&& (sm * m))
  outStrip n size hash acc

public meta def vrow0 (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let sm := spreadMask n
  let mut acc := 0
  for t in [0:args.size - 3] do
    acc := acc ||| ((← stripArg s!"X{t}" args[3 + t]!) &&& sm) <<< t
  outStrip n size hash acc

public meta def vbase (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let #[_, _, _, .nat c, .nat m, v] := args | throw "vbase: arguments"
  let x ← match v with
    | .nat v => do
      unless v >>> n == 0 do throw s!"vbase: vector past column {n}"
      pure (spreadVec n v)
    | _ => do pure ((← stripArg "v" v) &&& spreadMask n)
  outStrip n size hash (c ||| x * m)

public meta def vorbit (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let #[_, _, _, mv, .nat m] := args | throw "vorbit: arguments"
  unless 0 < m && m ≤ 64 do throw s!"vorbit: {m} rows"
  let M ← matRows "M" n mv
  let mut R : Array Nat := #[1]
  for _ in [1:m] do
    R := R.push (vecRows n M R.back!)
  outStrip n size hash (rowsStrip n R)

end CFSG.KC.BM.Twin
