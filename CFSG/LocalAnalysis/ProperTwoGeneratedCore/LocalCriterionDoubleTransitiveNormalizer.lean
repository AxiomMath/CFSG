module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerFlips
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPrimeNormalizerProper

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI
open LocalCriterionGeometry LocalCriterionInvariantNormalizer LocalCriterionMaximalPrime
open LocalCriterionDoubleTransitiveNormalizer

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_triple_sylow_normalizer_double_transitivity
    (H : Subgroup G) (z : G) (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (P : Sylow p (triplePointStabilizer H z beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)) :
    let U : Subgroup G := (P : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    let Delta := pointFixedSet H U
    let N := Subgroup.normalizer (U : Set G)
    (rightCosetMk H 1 ≠ beta ∧ rightCosetMk H 1 ≠ pointRightCosetMul H beta z ∧
      beta ≠ pointRightCosetMul H beta z) ∧
    (rightCosetMk H 1 ∈ Delta ∧ beta ∈ Delta ∧ pointRightCosetMul H beta z ∈ Delta) ∧
    (∀ a b : pointRightCosetSpace H, a ≠ rightCosetMk H 1 → b ≠ rightCosetMk H 1 →
      ∃ c ∈ Subgroup.centralizer ({z} : Set G), pointRightCosetMul H a c = b) ∧
    (¬ N ≤ H) ∧
    (∀ a b c d : pointRightCosetSpace H, a ∈ Delta → b ∈ Delta → c ∈ Delta → d ∈ Delta →
      a ≠ b → c ≠ d → ∃ n : G, n ∈ N ∧ pointRightCosetMul H a n = c ∧ pointRightCosetMul H b n = d) ∧
    InvolutionPointLocalEmbedding (H.subgroupOf N) (⟨z, hzP⟩ : N) ∧
    (∃ (T : Sylow 2 N) (hzT : (⟨z, hzP⟩ : N) ∈ (T : Subgroup N)),
      (⟨(⟨z, hzP⟩ : N), hzT⟩ : (T : Subgroup N)) ∈ Subgroup.center (T : Subgroup N)) ∧
    (∃ e : pointRightCosetSpace (H.subgroupOf N) ≃ Delta,
      (∀ n : N, (e (rightCosetMk (H.subgroupOf N) n)).val = rightCosetMk H (n : G)) ∧
      (∀ a : pointRightCosetSpace (H.subgroupOf N), ∀ n : N,
        (e (pointRightCosetMul (H.subgroupOf N) a n)).val = pointRightCosetMul H (e a).val (n : G))) ∧
    (∀ a b : pointRightCosetSpace H, a ∈ Delta → b ∈ Delta → a ≠ b →
      ∃ n : N, pointRightCosetMul H a (rightConjugateElem z (n : G)) = b ∧
        pointRightCosetMul H b (rightConjugateElem z (n : G)) = a) ∧
    (IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → U ≠ ⊥ → N ≠ ⊤) := by
  let U : Subgroup G := (P : Subgroup (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  have hUH : U ≤ H := (Subgroup.map_subtype_le _).trans
    ((show triplePointStabilizer H z beta ≤ pairPointStabilizer H beta from inf_le_left).trans
      (pairPointStabilizer_le_point H beta))
  have ha := original_triple_sylow_normalizer_action h S hzS hzcenter hdoubly beta hbeta p hp P hzP
  obtain ⟨hl, hcentral⟩ := original_triple_sylow_normalizer_local_datum h S hzS hzcenter beta hbeta p hp P hzP
  have ht := original_triple_sylow_normalizer_transitive h S hzS hzcenter hdoubly beta hbeta p hp P hzP
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.2.2, hl, hcentral,
    ⟨normalizerRightCosetFixedEquiv H U hUH ht, ?_, ?_⟩,
    original_triple_sylow_normalizer_every_pair_class_flip h S hzS hzcenter hdoubly beta hbeta p hp P hzP, ?_⟩
  · exact normalizerRightCosetFixedEquiv_mk H U hUH ht
  · exact normalizerRightCosetFixedEquiv_equivariant H U hUH ht
  · intro hsimple hnonab hU
    let : IsSimpleGroup G := hsimple
    exact prime_subgroup_normalizer_ne_top hnonab p hp U (P.isPGroup'.map _) hU

end CFSG.ProperTwoGeneratedCore
