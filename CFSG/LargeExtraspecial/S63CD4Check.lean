module

public import CFSG.LargeExtraspecial.S63CD4Rep
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Std.Data.HashMap
public meta import CFSG.LargeExtraspecial.S63CD4Rep
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.LargeExtraspecial.S63

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

@[expose] def mulR (X Y : Array ℕ) : Array ℕ := mulRows 24 X Y

@[expose] def conjR (g x : Array ℕ) : Array ℕ := mulR (mulR g x) g

@[expose] def oneR : Array ℕ := idRows 24

@[expose] def wordR (gs : Array (Array ℕ)) (w : List ℕ) : Array ℕ :=
  w.foldr (fun k acc => mulR gs[k]! acc) oneR

@[expose] def sq12R (x : Array ℕ) : Array ℕ :=
  (List.range 12).foldl (fun acc _ => mulR acc acc) x

@[expose] def classTreeOK (gs : Array (Array ℕ)) (x : Array ℕ) (T : Array (Array ℕ))
    (P K : Array ℕ) (idx : Array ℕ → ℕ) : Bool :=
  decide (0 < T.size) && T[0]! == x &&
  allLt T.size (fun i => validR T[i]! && idx T[i]! == i &&
    (i == 0 || (decide (P[i]! < i) && decide (K[i]! < gs.size) &&
      T[i]! == conjR gs[K[i]!]! T[P[i]!]!)))

@[expose] def enumOK (gs : Array (Array ℕ)) (El : Array (Array ℕ)) (P K : Array ℕ)
    (idx : Array ℕ → ℕ) : Bool :=
  decide (0 < El.size) && El[0]! == oneR &&
  allLt El.size (fun i => validR El[i]! && idx El[i]! == i &&
    (i == 0 || (decide (P[i]! < i) && decide (K[i]! < gs.size) &&
      El[i]! == mulR gs[K[i]!]! El[P[i]!]!)) &&
    allLt gs.size (fun k => let y := mulR gs[k]! El[i]!; decide (idx y < El.size) &&
      El[idx y]! == y))

@[expose] def memR (El : Array (Array ℕ)) (idx : Array ℕ → ℕ) (y : Array ℕ) : Bool :=
  decide (idx y < El.size) && El[idx y]! == y

@[expose] def marks (n : ℕ) (idx : Array ℕ → ℕ) (ps : List (Array ℕ)) : Array Bool :=
  ps.foldl (fun m p => m.set! (idx p) true) (Array.replicate n false)

@[expose] def coverOK (El : Array (Array ℕ)) (idx : Array ℕ → ℕ) (ps : List (Array ℕ)) : Bool :=
  let m := marks El.size idx ps
  ps.all (memR El idx) && allLt El.size fun j => m[j]!

@[expose] def subProds : List (Array ℕ) → List (Array ℕ)
  | [] => [oneR]
  | y :: ys => let r := subProds ys; r ++ r.map (mulR y)

@[expose] def mkIdx (L : Array (Array ℕ)) : Std.HashMap (Array ℕ) ℕ := Id.run do
  let mut m : Std.HashMap (Array ℕ) ℕ := {}
  for i in [0:L.size] do
    m := m.insert L[i]! i
  return m

@[expose] def lookup (m : Std.HashMap (Array ℕ) ℕ) (y : Array ℕ) : ℕ := m.getD y 0

@[expose] def classBFS (gs : Array (Array ℕ)) (x : Array ℕ) :
    Array (Array ℕ) × Array ℕ × Array ℕ := Id.run do
  let mut seen : Std.HashMap (Array ℕ) Unit := {}
  seen := seen.insert x ()
  let mut T : Array (Array ℕ) := #[x]
  let mut P : Array ℕ := #[0]
  let mut K : Array ℕ := #[0]
  let mut i := 0
  while i < T.size do
    let y := T[i]!
    for k in [0:gs.size] do
      let c := conjR gs[k]! y
      if !seen.contains c then
        seen := seen.insert c ()
        T := T.push c
        P := P.push i
        K := K.push k
    i := i + 1
  return (T, P, K)

@[expose] def enumBFS (gs : Array (Array ℕ)) : Array (Array ℕ) × Array ℕ × Array ℕ := Id.run do
  let mut seen : Std.HashMap (Array ℕ) Unit := {}
  seen := seen.insert oneR ()
  let mut T : Array (Array ℕ) := #[oneR]
  let mut P : Array ℕ := #[0]
  let mut K : Array ℕ := #[0]
  let mut i := 0
  while i < T.size do
    let y := T[i]!
    for k in [0:gs.size] do
      let c := mulR gs[k]! y
      if !seen.contains c then
        seen := seen.insert c ()
        T := T.push c
        P := P.push i
        K := K.push k
    i := i + 1
  return (T, P, K)

end CFSG.LargeExtraspecial.S63
