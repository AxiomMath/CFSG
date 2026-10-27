module

public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Std.Data.HashMap
public meta import CFSG.Monster.B.Co2.PermArr
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Std.Data.HashMap
public import Mathlib.Data.Vector.Basic
public meta import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8D8

open CFSG.Monster.B.Co2.Native

@[expose] def letT (n : ℕ) (A B U : Array ℕ) (l : ℕ) : Array ℕ :=
  if l = 0 then A else if l = 1 then B else if l = 2 then invCand n A
    else if l = 3 then invCand n B else U

@[expose] def wordT (n : ℕ) (A B U : Array ℕ) (w : List ℕ) : Array ℕ :=
  w.foldl (fun acc l => compA n acc (letT n A B U l)) (idA n)

@[expose] def gensT (n : ℕ) (A B U : Array ℕ) (ws : List (List ℕ)) : Array (Array ℕ) :=
  (ws.map (wordT n A B U)).toArray

@[expose] def bfsT (n : ℕ) (gens : Array (Array ℕ)) : Array (Array ℕ) × Array ℕ × Array ℕ :=
  Id.run do
  let mut E : Array (Array ℕ) := #[idA n]
  let mut par : Array ℕ := #[0]
  let mut gen : Array ℕ := #[0]
  let mut idx : Std.HashMap (Array ℕ) ℕ := {}
  idx := idx.insert (idA n) 0
  for i in [0:256] do
    if i < E.size then
      for k in [0:gens.size] do
        let c := compA n E[i]! gens[k]!
        if !idx.contains c then
          idx := idx.insert c E.size
          E := E.push c
          par := par.push i
          gen := gen.push k
  return (E, par, gen)

@[expose] def idxT (E : Array (Array ℕ)) : Std.HashMap (Array ℕ) ℕ := Id.run do
  let mut m : Std.HashMap (Array ℕ) ℕ := {}
  for k in [0:E.size] do
    m := m.insert E[k]! k
  return m

@[expose] def mulTabT (n : ℕ) (E : Array (Array ℕ)) (idx : Std.HashMap (Array ℕ) ℕ) :
    Array (Array ℕ) := Id.run do
  let mut T : Array (Array ℕ) := #[]
  for a in [0:256] do
    let mut row : Array ℕ := #[]
    for b in [0:256] do
      row := row.push (idx.getD (compA n E[a]! E[b]!) 0)
    T := T.push row
  return T

@[expose] def invTabT (n : ℕ) (E : Array (Array ℕ)) (idx : Std.HashMap (Array ℕ) ℕ) :
    Array ℕ := Id.run do
  let mut T : Array ℕ := #[]
  for a in [0:256] do
    T := T.push (idx.getD (invCand n E[a]!) 0)
  return T

@[expose] def mulIx (M : Array (Array ℕ)) (a b : ℕ) : ℕ := (M[a]!)[b]!

@[expose] def invIx (I : Array ℕ) (a : ℕ) : ℕ := I[a]!

@[expose] def ord4Ix (M : Array (Array ℕ)) (a : ℕ) : Bool :=
  mulIx M (mulIx M a a) (mulIx M a a) == 0 && mulIx M a a != 0

@[expose] def involInvIx (M : Array (Array ℕ)) (I : Array ℕ) (b a : ℕ) : Bool :=
  mulIx M b b == 0 && mulIx M (mulIx M b a) (invIx I b) == invIx I a

@[expose] def commIx (M : Array (Array ℕ)) (a c : ℕ) : Bool := mulIx M a c == mulIx M c a

@[expose] def quadIx (M : Array (Array ℕ)) (I : Array ℕ) (a b c d : ℕ) : Bool :=
  ord4Ix M a && involInvIx M I b a && ord4Ix M c && commIx M a c && commIx M b c &&
    (mulIx M a a != mulIx M c c) && involInvIx M I d c && commIx M a d && commIx M b d

@[expose] def searchD8 (M : Array (Array ℕ)) (I : Array ℕ) : Bool :=
  allLt 256 fun a => !ord4Ix M a ||
    allLt 256 fun b => !involInvIx M I b a ||
      allLt 256 fun c => !(ord4Ix M c && commIx M a c && commIx M b c &&
          (mulIx M a a != mulIx M c c)) ||
        allLt 256 fun d => !(involInvIx M I d c && commIx M a d && commIx M b d)

@[expose] def sizeOKT (E : Array (Array ℕ)) : Bool := E.size == 256

@[expose] def idOKT (n : ℕ) (E : Array (Array ℕ)) : Bool := eqA n E[0]! (idA n)

@[expose] def permOKT (n : ℕ) (E : Array (Array ℕ)) : Bool :=
  allLt 256 fun a => isInvA n E[a]! (invCand n E[a]!)

@[expose] def distinctOKT (n : ℕ) (E : Array (Array ℕ)) : Bool :=
  allLt 256 fun a => allLt a fun b => !eqA n E[a]! E[b]!

@[expose] def genOKT (n : ℕ) (E gens : Array (Array ℕ)) (par gen : Array ℕ) : Bool :=
  allLt 256 fun a => a == 0 || (par[a]! < a && gen[a]! < gens.size &&
    eqA n (compA n E[par[a]!]! gens[gen[a]!]!) E[a]!)

@[expose] def mulOKT (n : ℕ) (E M : Array (Array ℕ)) : Bool :=
  allLt 256 fun a => allLt 256 fun b =>
    (M[a]!)[b]! < 256 && eqA n (compA n E[a]! E[b]!) E[(M[a]!)[b]!]!

@[expose] def invOKT (n : ℕ) (E : Array (Array ℕ)) (I : Array ℕ) : Bool :=
  allLt 256 fun a => I[a]! < 256 && eqA n (invCand n E[a]!) E[I[a]!]!

@[expose] def checkD8 (n : ℕ) (A B U : Array ℕ) (ws : List (List ℕ)) : Bool :=
  let gens := gensT n A B U ws
  let r := bfsT n gens
  let E := r.1
  let idx := idxT E
  let M := mulTabT n E idx
  let I := invTabT n E idx
  isInvA n A (invCand n A) && isInvA n B (invCand n B) && isInvA n U (invCand n U) &&
    sizeOKT E && idOKT n E && permOKT n E && distinctOKT n E && genOKT n E gens r.2.1 r.2.2 &&
    mulOKT n E M && invOKT n E I && searchD8 M I

end CFSG.EvenSporadicStandard.Fin76b.TS8D8
