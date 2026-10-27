module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.ConjFinCheck

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.SeitzGeneration.ExcWideThree

@[expose] def trWit (κs : List (List ℕ)) (β3 : List (List ℕ)) : Bool :=
  κs.any fun κ =>
    let m := rfMOf κ
    rfModEq3 (rfCartanMod3.map fun row => rfDotN row m) κ && !(rfModEq3 (rfLincomb3 m β3) m)

@[expose] def trLeafOK (ω : List ℕ) (k₁ k₂ : List ℕ) (β : List (List ℤ)) : Bool :=
  let β3 := β.map (·.map rfRes3)
  !(rfCCond β3) || rfRhoComm (rfConjCols ω β) || trWit (rfPlaneVecs k₁ k₂) β3

@[expose] def trHPlaneCheck (k₁ k₂ : List ℕ) (ω : List ℕ) : Bool :=
  (rfLeaves ((List.range 6).map (rfCands k₁ k₂)) 6 []).all (trLeafOK ω k₁ k₂)

theorem trHPlanes_true :
    rfHTable.all (fun t => trHPlaneCheck t.1 t.2.1 t.2.2) = true := by
  decide +kernel

end CFSG.LieType.SeitzGeneration.ExcHighThree
