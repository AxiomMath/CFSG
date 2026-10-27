module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyGHCent

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

theorem eq_of_mem_center_of_orderOf_eq_two {P : Type*} [Group P]
    (ι : P ≃* RegularWreathProduct (DihedralGroup 4) (Multiplicative (ZMod 2))) {a b : P}
    (ha : a ∈ Subgroup.center P) (hb : b ∈ Subgroup.center P) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) : a = b :=
  SAFyGH.center_unique ι ha hb (fun h => by simp [h] at ha2) (fun h => by simp [h] at hb2)

end CFSG.EvenSporadicStandard.TwoHS.GH312
