module

public import Certificates.Data.HNUnitaryBridge

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

@[expose] def gen5aPt (w : List Nat) (x : Nat) : Nat :=
  w.foldr (fun l a => (HNUnitaryBridge.smallPermLists[l]!)[a]!) x

@[expose] def gen5aEq (u v : List Nat) : Bool :=
  u.all (· < 6) && v.all (· < 6) && (List.range 50).all fun x => gen5aPt u x == gen5aPt v x

@[expose] def gen5aWt : List Nat := [0, 1]

@[expose] def gen5aWt' : List Nat := [1, 0]

@[expose] def gen5aWy₁ : List Nat := [5, 4, 1, 3, 2]

@[expose] def gen5aWy₂ : List Nat := [2, 1, 4, 0, 2]

@[expose] def gen5aExp (w : List Nat) : List Nat :=
  w.flatMap fun l => if l = 0 then gen5aWy₁ else gen5aWy₂

@[expose] def gen5aWords : List (List Nat) :=
  [[1, 0, 0, 0, 1, 1, 0, 0, 1, 1],
   [0, 0, 0, 1, 1, 0, 0, 1, 1, 1],
   [0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0],
   [1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
   [0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0],
   [1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1]]

@[expose] def gen5aOK : Bool :=
  gen5aEq (gen5aWt ++ gen5aWt) [] && !gen5aEq gen5aWt [] &&
    gen5aEq (gen5aWt' ++ gen5aWt') [] && !gen5aEq gen5aWt' [] && !gen5aEq gen5aWt gen5aWt' &&
    gen5aEq (gen5aWt ++ gen5aWt') (gen5aWt' ++ gen5aWt) &&
    gen5aEq (gen5aWy₁ ++ gen5aWt) (gen5aWt ++ gen5aWy₁) &&
    gen5aEq (gen5aWy₂ ++ gen5aWt') (gen5aWt' ++ gen5aWy₂) && gen5aWords.length == 6 &&
    (List.range 6).all fun k => gen5aEq (gen5aExp (gen5aWords.getD k [])) [k]

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
