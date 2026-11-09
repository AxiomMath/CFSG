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

theorem trAll_take_drop {α : Type} (l : List α) (k : ℕ) (f : α → Bool) :
    l.all f = ((l.take k).all f && (l.drop k).all f) := by
  rw [← List.all_append, List.take_append_drop]

theorem trHPlanes_0 : (rfHTable.take 10).all
    (fun t => trHPlaneCheck t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem trHPlanes_1 : ((rfHTable.drop 10).take 10).all
    (fun t => trHPlaneCheck t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem trHPlanes_2 : (((rfHTable.drop 10).drop 10).take 10).all
    (fun t => trHPlaneCheck t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem trHPlanes_3 : (((rfHTable.drop 10).drop 10).drop 10).all
    (fun t => trHPlaneCheck t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem trHPlanes_true : rfHTable.all (fun t => trHPlaneCheck t.1 t.2.1 t.2.2) = true := by
  rw [trAll_take_drop rfHTable 10, trAll_take_drop (rfHTable.drop 10) 10,
    trAll_take_drop ((rfHTable.drop 10).drop 10) 10, trHPlanes_0, trHPlanes_1, trHPlanes_2,
    trHPlanes_3]
  all_goals decide

end CFSG.LieType.SeitzGeneration.ExcHighThree
