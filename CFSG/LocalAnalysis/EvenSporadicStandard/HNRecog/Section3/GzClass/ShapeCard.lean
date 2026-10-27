module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem natCard_Z (n : ℕ) [NeZero n] : Nat.card (Z n) = n := by
  rw [Nat.card_congr (Multiplicative.toAdd : Z n ≃ ZMod n), Nat.card_zmod]

theorem card_of_isShapeZ2TimesA5 {X : Type*} [Group X] (h : IsShapeZ2TimesA5 X) :
    Nat.card X = 120 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, natCard_Z, nat_card_alternatingGroup,
    Nat.card_fin]
  norm_num

theorem card_of_isShapeTwoTwoTimesA5 {X : Type*} [Group X] (h : IsShapeTwoTwoTimesA5 X) :
    Nat.card X = 240 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_Elem2_eq, nat_card_alternatingGroup,
    Nat.card_fin]
  norm_num

theorem card_of_isShapeTwoTwoWrTwo {X : Type*} [Group X] (h : IsShapeTwoTwoWrTwo X) :
    Nat.card X = 32 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, card_Elem2_eq, natCard_Z]
  norm_num

theorem card_of_isShapeZpTimesZp_five {X : Type*} [Group X] (h : IsShapeZpTimesZp 5 X) :
    Nat.card X = 25 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, natCard_Z]

theorem card_of_isShapeZpWrTwo_five {X : Type*} [Group X] (h : IsShapeZpWrTwo 5 X) :
    Nat.card X = 50 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, natCard_Z, natCard_Z]
  norm_num

end CFSG.EvenSporadicStandard.HNRecog.Section3
