module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagFin

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree

@[expose] def rfRefl (i : ℕ) (x : List ℤ) : List ℤ :=
  x.set i (x.getD i 0 - rfDotL (rfCartanL.getD i []) x)

@[expose] def rfWordApply (ω : List ℕ) (x : List ℤ) : List ℤ := ω.foldr rfRefl x

@[expose] def rfVCols (ω : List ℕ) : List (List ℤ) :=
  (List.range 6).map fun j => rfWordApply ω (rfUnit j)

@[expose] def rfRho (i : ℕ) : ℕ := [5, 1, 4, 3, 2, 0].getD i 0

@[expose] def rfConjCols (ω : List ℕ) (β : List (List ℤ)) : List (List ℤ) :=
  (rfVCols ω.reverse).map fun c => rfLincombZ (rfLincombZ c β) (rfVCols ω)

@[expose] def rfRhoComm (X : List (List ℤ)) : Bool :=
  (List.range 6).all fun j => (List.range 6).all fun i =>
    (X.getD (rfRho j) []).getD i 0 == (X.getD j []).getD (rfRho i) 0

@[expose] def rfInvFix (ω : List ℕ) (κ : List ℕ) : Bool :=
  (List.range 6).all fun i =>
    (rfDotL (κ.map fun x : ℕ => (x : ℤ)) ((rfVCols ω.reverse).getD (rfRho i) []) -
      rfDotL (κ.map fun x : ℕ => (x : ℤ)) ((rfVCols ω.reverse).getD i [])) % 3 == 0

@[expose] def rfWitCands : List (List ℕ) :=
  [[0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 2], [0, 0, 0, 1, 2, 1], [0, 1, 1, 0, 1, 2],
    [0, 1, 2, 0, 0, 0]]

@[expose] def rfWitness (β3 : List (List ℕ)) : Bool :=
  rfWitCands.any fun m =>
    let k := rfCartanMod3.map fun row => rfDotN row m % 3
    (List.range 6).all (fun t => rfDotN k (β3.getD t []) % 3 == k.getD t 0 % 3) &&
      !(rfModEq3 (rfLincomb3 m β3) m)

@[expose] def rfHLeafOK (ω : List ℕ) (β : List (List ℤ)) : Bool :=
  let β3 := β.map (·.map rfRes3)
  !(rfCCond β3) || rfHasFix β || (rfRhoComm (rfConjCols ω β) && rfWitness β3)

@[expose] def rfHPlaneCheck (k₁ k₂ : List ℕ) (ω : List ℕ) : Bool :=
  rfInvFix ω k₁ && rfInvFix ω k₂ &&
    (rfLeaves ((List.range 6).map (rfCands k₁ k₂)) 6 []).all (rfHLeafOK ω)

@[expose] def rfHTable : List (List ℕ × List ℕ × List ℕ) :=
[
  ([0, 0, 0, 1, 0, 0], [1, 1, 1, 0, 1, 1], []),
  ([0, 0, 0, 1, 0, 0], [1, 1, 1, 0, 2, 2], [0]),
  ([0, 0, 0, 1, 0, 0], [1, 2, 1, 0, 1, 1], []),
  ([0, 0, 0, 1, 0, 0], [1, 2, 1, 0, 2, 2], [0]),
  ([0, 0, 1, 0, 1, 0], [1, 1, 0, 1, 0, 1], []),
  ([0, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 2], [0]),
  ([0, 0, 1, 0, 1, 0], [1, 2, 0, 2, 0, 1], []),
  ([0, 0, 1, 0, 1, 0], [1, 2, 0, 2, 1, 2], [0]),
  ([0, 0, 1, 1, 0, 2], [1, 1, 0, 1, 1, 2], [0, 2]),
  ([0, 0, 1, 1, 0, 2], [1, 1, 0, 2, 2, 0], [4, 3]),
  ([0, 0, 1, 1, 0, 2], [1, 2, 0, 0, 2, 0], [5, 2, 0]),
  ([0, 0, 1, 1, 0, 2], [1, 2, 0, 2, 1, 2], [0, 2]),
  ([0, 0, 1, 1, 2, 1], [1, 1, 0, 1, 0, 1], [4]),
  ([0, 0, 1, 1, 2, 1], [1, 1, 0, 2, 2, 0], [2, 0]),
  ([0, 0, 1, 1, 2, 1], [1, 2, 0, 0, 2, 0], [2, 0]),
  ([0, 0, 1, 1, 2, 1], [1, 2, 0, 2, 0, 1], [4]),
  ([0, 1, 1, 0, 0, 2], [1, 0, 0, 1, 1, 2], [0, 2]),
  ([0, 1, 1, 0, 0, 2], [1, 0, 0, 2, 2, 0], [5, 2, 0]),
  ([0, 1, 1, 0, 0, 2], [1, 0, 2, 1, 1, 0], [0, 2]),
  ([0, 1, 1, 0, 0, 2], [1, 0, 2, 2, 2, 1], [5, 2, 0]),
  ([0, 1, 1, 0, 2, 1], [1, 0, 0, 1, 0, 1], [4]),
  ([0, 1, 1, 0, 2, 1], [1, 0, 0, 2, 2, 0], [2, 0]),
  ([0, 1, 1, 0, 2, 1], [1, 0, 2, 1, 1, 0], [4]),
  ([0, 1, 1, 0, 2, 1], [1, 0, 2, 2, 0, 2], [2, 0]),
  ([0, 1, 1, 2, 1, 0], [1, 0, 0, 1, 0, 1], []),
  ([0, 1, 1, 2, 1, 0], [1, 0, 0, 1, 1, 2], [0]),
  ([0, 1, 1, 2, 1, 0], [1, 0, 2, 2, 0, 2], [0]),
  ([0, 1, 1, 2, 1, 0], [1, 0, 2, 2, 2, 1], []),
  ([0, 1, 2, 0, 2, 0], [1, 0, 0, 1, 0, 1], []),
  ([0, 1, 2, 0, 2, 0], [1, 0, 0, 1, 1, 2], [0]),
  ([0, 1, 2, 0, 2, 0], [1, 0, 2, 2, 0, 2], [0]),
  ([0, 1, 2, 0, 2, 0], [1, 0, 2, 2, 2, 1], []),
  ([0, 1, 2, 2, 0, 1], [1, 0, 0, 1, 1, 2], [0, 2]),
  ([0, 1, 2, 2, 0, 1], [1, 0, 0, 2, 2, 0], [4, 3]),
  ([0, 1, 2, 2, 0, 1], [1, 0, 2, 1, 1, 0], [0, 2]),
  ([0, 1, 2, 2, 0, 1], [1, 0, 2, 2, 2, 1], [5, 2, 0]),
  ([0, 1, 2, 2, 1, 2], [1, 0, 0, 1, 0, 1], [4]),
  ([0, 1, 2, 2, 1, 2], [1, 0, 0, 2, 2, 0], [2, 0]),
  ([0, 1, 2, 2, 1, 2], [1, 0, 2, 1, 1, 0], [4]),
  ([0, 1, 2, 2, 1, 2], [1, 0, 2, 2, 0, 2], [2, 0])]

theorem rfHTable_planes : rfHTable.map (fun t => (t.1, t.2.1)) = rfPlaneBases := by
  decide +kernel

theorem rfHPlanes_true :
    rfHTable.all (fun t => rfHPlaneCheck t.1 t.2.1 t.2.2) = true := by
  decide +kernel

end CFSG.LieType.SeitzGeneration.ExcWideThree
