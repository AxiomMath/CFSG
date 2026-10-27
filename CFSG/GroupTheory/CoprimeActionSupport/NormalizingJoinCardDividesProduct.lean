module


public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct

variable {G : Type*} [Group G]

theorem card_dvd_product [Finite G] (H K : Subgroup G) (hK : K ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card (H ⊔ K : Subgroup G) ∣ Nat.card H * Nat.card K := by
  have card_mul_intersection [Finite G] (H K : Subgroup G) (hK : K ≤ Subgroup.normalizer (H : Set G)) :
      Nat.card (H ⊔ K : Subgroup G) * Nat.card (H ⊓ K : Subgroup G) =
        Nat.card H * Nat.card K := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hK
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hK
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient K H hK
    have h1 : Nat.card (K ⧸ H.subgroupOf K) =
        Nat.card ((K ⊔ H : Subgroup G) ⧸ H.subgroupOf (K ⊔ H)) := Nat.card_congr e.toEquiv
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (K ⊔ H))
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf K)
    have h4 : ∀ L : Subgroup G, Nat.card (H.subgroupOf L) = Nat.card (H ⊓ L : Subgroup G) := by
      intro L
      rw [← Subgroup.subgroupOf_map_subtype H L,
        Subgroup.card_map_of_injective L.subtype_injective]
    have h5 : Nat.card (H.subgroupOf (K ⊔ H)) = Nat.card H := by
      rw [h4, inf_of_le_left (le_sup_right : H ≤ K ⊔ H)]
    rw [h5] at h2
    rw [h4] at h3
    rw [sup_comm H K, h2, h3, ← h1]
    ring
  exact Dvd.intro _ (card_mul_intersection H K hK)

end CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct
