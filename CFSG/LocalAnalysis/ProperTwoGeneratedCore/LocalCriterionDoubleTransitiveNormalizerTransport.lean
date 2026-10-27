module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerEscape
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerCentralizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

attribute [local instance] pointRightCosetOppositeMulAction

variable {G : Type*} [Group G] [Finite G]

theorem original_triple_sylow_normalizer_action
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
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
    (rightCosetMk H 1 ≠ beta ∧
      rightCosetMk H 1 ≠ pointRightCosetMul H beta z ∧
      beta ≠ pointRightCosetMul H beta z) ∧
    (rightCosetMk H 1 ∈ Delta ∧ beta ∈ Delta ∧ pointRightCosetMul H beta z ∈ Delta) ∧
    (∀ a b : pointRightCosetSpace H, a ≠ rightCosetMk H 1 → b ≠ rightCosetMk H 1 →
      ∃ c ∈ Subgroup.centralizer ({z} : Set G), pointRightCosetMul H a c = b) ∧
    (¬ N ≤ H) ∧
    (∀ n : G, n ∈ N → ∀ a : pointRightCosetSpace H,
      a ∈ Delta → pointRightCosetMul H a n ∈ Delta) ∧
    (∀ a b : pointRightCosetSpace H, a ∈ Delta → b ∈ Delta →
      a ≠ rightCosetMk H 1 → b ≠ rightCosetMk H 1 →
      ∃ n : G, n ∈ N ⊓ H ∧ pointRightCosetMul H a n = b) ∧
    (∀ a b c d : pointRightCosetSpace H,
      a ∈ Delta → b ∈ Delta → c ∈ Delta → d ∈ Delta →
      a ≠ b → c ≠ d →
      ∃ n : G, n ∈ N ∧ pointRightCosetMul H a n = c ∧ pointRightCosetMul H b n = d) := by
  have hunique : ∀ a : pointRightCosetSpace H, rightAct a z = a ↔ a = rightCosetMk H 1 :=
    ((involution_point_unique_containment_action h.distinguished_mem h.distinguished_order).2
      h.unique_containment).2.2.1
  have hcentral := full_centralizer_transitive_on_original_nonbase_points h S hzS hzcenter hdoubly
  have hcentral' : ∀ a b : pointRightCosetSpace H,
      a ≠ rightCosetMk H 1 → b ≠ rightCosetMk H 1 →
      ∃ c ∈ Subgroup.centralizer ({z} : Set G), rightAct a c = b := hcentral
  have habstract := centralizer_transitive_triple_sylow_normalizer_action
    z (rightCosetMk H 1) beta
    (show IsInvolution z from ⟨by
      intro hz1
      have hh := h.distinguished_order
      rw [hz1, orderOf_one] at hh
      omega,
      pow_orderOf_eq_one z |> fun hh => h.distinguished_order ▸ hh⟩)
    hunique hcentral' hbeta p hp
  rw [point_tripleStabilizer_eq H z beta] at habstract
  have hresult := habstract P hzP
  simp only [point_rightAct_eq, point_rightFixedSet_eq, point_rightStabilizer_eq,
    rightCosetStabilizer_base] at hresult
  have hescape := triple_sylow_normalizer_not_le_original_point h S hzS hzcenter hbeta p hp P
  exact ⟨hresult.1, hresult.2.1, hcentral, hescape, hresult.2.2.1,
    hresult.2.2.2.1, hresult.2.2.2.2 hescape⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
