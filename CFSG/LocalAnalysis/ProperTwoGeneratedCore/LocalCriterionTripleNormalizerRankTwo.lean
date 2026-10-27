module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentral
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerHull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open LocalCriterionGeometry LocalCriterionInvariantNormalizer LocalCriterionMaximalPrime
open LocalCriterionDoubleTransitiveNormalizer

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_triple_sylow_normalizer_involution_hull_rank_two
    (H : Subgroup G) (z : G) (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hambient : ∀ Q : Sylow p G, Nat.card (pointFixedSet H (Q : Subgroup G)) = 2)
    (P : Sylow p (triplePointStabilizer H z beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)) :
    let U : Subgroup G := (P : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    let N := Subgroup.normalizer (U : Set G)
    Nat.card (pointFixedSet H U) ≡ 2 [MOD p] ∧
      (¬ ∃ Q : Sylow p G, (Q : Subgroup G) = U) ∧
      (¬ ∃ Q : Sylow p N, (Q : Subgroup N).map N.subtype = U) ∧
      QuotientGroup.mk' (CFSG.oddCore N) (⟨z, hzP⟩ : N) ∉
        Subgroup.center (N ⧸ CFSG.oddCore N) ∧
      2 ≤ CFSG.Open.pRank 2 (Subgroup.closure (conjugacyWithin N z)) := by
  have hstats := original_triple_sylow_full_fixed_count_and_sylow_obstructions
    h S hzS hzcenter hdoubly beta hbeta p hp hambient P hzP
  have hnoncentral := local_involution_point_triple_sylow_normalizer_noncentral_odd_quotient
    h S hzS hzcenter hdoubly beta hbeta p hp hodd hambient P hzP
  refine ⟨hstats.1, hstats.2.2.1, hstats.2.2.2, hnoncentral, ?_⟩
  exact original_subgroup_class_hull_rank_two_of_noncentral_odd_quotient
    _ z hzP h.distinguished_order hnoncentral

end CFSG.ProperTwoGeneratedCore
