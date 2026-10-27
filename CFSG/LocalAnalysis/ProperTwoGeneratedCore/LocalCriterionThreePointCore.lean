module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthCover
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthPair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowCounting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open scoped Pointwise

variable {G : Type*} [Group G]

theorem subgroup_sup_eq_of_literal_product (J E F : Subgroup G)
    (hproduct : (F : Set G) = (J : Set G) * (E : Set G)) : J ⊔ E = F := by
  rw [Subgroup.sup_eq_closure_mul, ← hproduct, Subgroup.closure_eq]

theorem triple_odd_core_eq_pair_intersection [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    (CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype =
      pairOddCore H beta ⊓ triplePointStabilizer H z beta := by
  obtain ⟨t, ht⟩ := original_pair_flip_exists h beta hbeta
  exact generatedPairGrowth_triple_odd_core_eq_intersection h S hzS hzcenter hbeta ht

theorem triple_odd_core_eq_opposite_pair_intersection [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    (CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype =
      oppositePairOddCore H z beta ⊓ triplePointStabilizer H z beta := by
  apply generatedPairGrowth_ambient_odd_core_eq_intersection_of_full_cover
    (oppositePairStabilizer H z beta) (triplePointStabilizer H z beta)
    (triple_stabilizer_le_opposite_pair H z beta)
  exact subgroup_sup_eq_of_literal_product _ _ _
    (opposite_pair_eq_odd_core_mul_triple h S hzS hzcenter beta hbeta)

theorem equal_order_overgroup_sylow_transfer [Finite G]
    (p : ℕ) (hp : p.Prime) (B E F : Subgroup G)
    (hEB : E ≤ B) (hEF : E ≤ F) (hFBcard : Nat.card F = Nat.card B)
    (hcontains : ∃ Q : Sylow p B, (Q : Subgroup B).map B.subtype ≤ E)
    (P : Sylow p E) :
    ∃ R : Sylow p F, (R : Subgroup F).map F.subtype = (P : Subgroup E).map E.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ := sylow_of_overgroup_with_contained_sylow p hp B E hEB hcontains P
  have hcard : Nat.card ((P : Subgroup E).map E.subtype) =
      p ^ (Nat.card F).factorization p := by
    rw [← hQ, Subgroup.card_subtype, Q.card_eq_multiplicity, hFBcard]
  exact p_subgroup_sylow_of_full_card p hp F ((P : Subgroup E).map E.subtype)
    ((Subgroup.map_subtype_le _).trans hEF) hcard

theorem triple_contains_opposite_pair_sylow [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime)
    (hcontains : ∃ Q : Sylow p (pairPointStabilizer H beta),
      (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta) :
    ∃ R : Sylow p (oppositePairStabilizer H z beta),
      (R : Subgroup (oppositePairStabilizer H z beta)).map
        (oppositePairStabilizer H z beta).subtype ≤ triplePointStabilizer H z beta := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := triplePointStabilizer H z beta)
  obtain ⟨R, hR⟩ := equal_order_overgroup_sylow_transfer p hp
    (pairPointStabilizer H beta) (triplePointStabilizer H z beta)
    (oppositePairStabilizer H z beta) inf_le_left
    (triple_stabilizer_le_opposite_pair H z beta)
    (opposite_pair_order_eq_pair h S hzS hzcenter beta hbeta) hcontains P
  exact ⟨R, by rw [hR]; exact Subgroup.map_subtype_le _⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
