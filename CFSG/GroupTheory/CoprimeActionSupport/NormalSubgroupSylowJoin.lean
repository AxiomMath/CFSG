module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf {H K : Subgroup G} (h : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card (H ⊔ K : Subgroup G) * Nat.card (H ⊓ K : Subgroup G) =
      Nat.card H * Nat.card K := by
  have hr : K.relIndex H = K.relIndex (H ⊔ K) := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer h
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K h).toEquiv
  have h1 := Subgroup.relIndex_mul_card K H
  have h2 := Subgroup.relIndex_mul_card K (H ⊔ K)
  rw [inf_eq_left.mpr (le_sup_right : K ≤ H ⊔ K)] at h2
  rw [inf_comm] at h1
  rw [← h2, ← h1, hr]
  ring

end CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
