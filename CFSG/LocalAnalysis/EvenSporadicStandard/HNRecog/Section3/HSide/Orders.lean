module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem card_Elem2_eq (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  change Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem card_of_isShapeTwoTwoTimesA8 {X : Type*} [Group X] (h : IsShapeTwoTwoTimesA8 X) :
    Nat.card X = 80640 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_Elem2_eq 2, nat_card_alternatingGroup,
    Nat.card_fin]
  norm_num

theorem card_of_isShapeTwoTwoSixS5 {X : Type*} [Group X] (h : IsShapeTwoTwoSixS5 X) :
    Nat.card X = 30720 := by
  obtain ⟨V, N, hVnorm, hNnorm, hVN, hVE, hNVE, hXNE⟩ := h
  haveI : V.Normal := hVnorm
  haveI : N.Normal := hNnorm
  haveI : (V.subgroupOf N).Normal := hVnorm.subgroupOf N
  have hcardV : Nat.card V = 2 ^ 2 := by
    rw [Nat.card_congr (Classical.choice hVE).toEquiv, card_Elem2_eq]
  have hcardNV : Nat.card (N ⧸ V.subgroupOf N) = 2 ^ 6 := by
    rw [Nat.card_congr (Classical.choice hNVE).toEquiv, card_Elem2_eq]
  have hcardN : Nat.card N = 2 ^ 8 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf N), hcardNV,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv, hcardV]
    norm_num
  have hcardXN : Nat.card (X ⧸ N) = 120 := by
    rw [Nat.card_congr (Classical.choice hXNE).toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hcardXN, hcardN]
  norm_num

end CFSG.EvenSporadicStandard.HNRecog.Section3
