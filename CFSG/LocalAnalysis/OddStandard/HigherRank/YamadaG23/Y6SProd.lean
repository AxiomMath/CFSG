module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {G : Type} [Group G]

theorem y6_card_sup_mul_inf [Finite G] {H N : Subgroup G} (hHN : H ≤ normalizer (N : Set G)) :
    Nat.card ↥(H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card ↥H * Nat.card ↥N := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  have h3 : Nat.card ↥(N.subgroupOf (H ⊔ N)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv
  have h4 : Nat.card ↥(N.subgroupOf H) = Nat.card ↥(H ⊓ N) := by
    rw [← Subgroup.inf_subgroupOf_left N H]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ N ≤ H)).toEquiv
  rw [← Nat.card_congr e.toEquiv, h3] at h1
  rw [h4] at h2
  rw [h1, h2]
  exact mul_right_comm _ _ _

end CFSG.OddStandard.HigherRank.YamadaG23
