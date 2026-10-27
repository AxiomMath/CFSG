module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Orders

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem card_of_isShapeTwoTwoTimesTwoFourA5 {X : Type*} [Group X]
    (h : IsShapeTwoTwoTimesTwoFourA5 X) : Nat.card X = 3840 := by
  obtain ⟨Y, _, hshape, hiso⟩ := h
  obtain ⟨e⟩ := hiso
  have hY : Nat.card Y = 16 * 60 := by
    obtain ⟨N, hN, hNiso, hQiso⟩ := hshape
    haveI : N.Normal := hN
    obtain ⟨eN⟩ := hNiso
    obtain ⟨eQ⟩ := hQiso
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv,
      Nat.card_congr eN.toEquiv, card_Elem2_eq 4, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_Elem2_eq 2, hY]
  norm_num

end CFSG.EvenSporadicStandard.HNRecog.Section3
