module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowCounting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

universe u

variable {G : Type u} [Group G] [Finite G]

theorem local_involution_point_three_point_sylow_criterion
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    z ∈ Subgroup.normalizer (triplePointStabilizer H z beta : Set G) ∧
    ∀ p : ℕ, p.Prime →
      (∀ X : Subgroup G, X ≤ pairPointStabilizer H beta → IsPGroup p X →
        z ∈ Subgroup.normalizer (X : Set G) →
        X ≤ triplePointStabilizer H z beta ∧
          ∃ P : Sylow p (triplePointStabilizer H z beta),
            X ≤ (P : Subgroup (triplePointStabilizer H z beta)).map
              (triplePointStabilizer H z beta).subtype ∧
            z ∈ Subgroup.normalizer
              (((P : Subgroup (triplePointStabilizer H z beta)).map
                (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G) ∧
            ∃ R : Sylow p (pairPointStabilizer H beta ⊓
              Subgroup.centralizer ({z} : Set G) : Subgroup G),
              (R : Subgroup (pairPointStabilizer H beta ⊓
                Subgroup.centralizer ({z} : Set G) : Subgroup G)).map
                  (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G)).subtype =
                (P : Subgroup (triplePointStabilizer H z beta)).map
                  (triplePointStabilizer H z beta).subtype ⊓ Subgroup.centralizer ({z} : Set G)) ∧
      ((∃ Q : Sylow p (pairPointStabilizer H beta),
        (Q : Subgroup (pairPointStabilizer H beta)).map (pairPointStabilizer H beta).subtype ≤
          triplePointStabilizer H z beta) ↔
        ∃ X : Subgroup G, X ≤ pairPointStabilizer H beta ∧ IsPGroup p X ∧
          z ∈ Subgroup.normalizer (X : Set G) ∧
          p ^ (Nat.card (conjugacyWithin H z)).factorization p ≤ Nat.card (conjugacyWithin X z)) ∧
      ((∃ Q : Sylow p (pairPointStabilizer H beta),
        (Q : Subgroup (pairPointStabilizer H beta)).map (pairPointStabilizer H beta).subtype ≤
          triplePointStabilizer H z beta) →
        ∃ X : Subgroup G, X ≤ pairPointStabilizer H beta ∧ IsPGroup p X ∧
          z ∈ Subgroup.normalizer (X : Set G) ∧
          Nat.card (conjugacyWithin X z) = p ^ (Nat.card (conjugacyWithin H z)).factorization p) := by
  refine ⟨triple_stabilizer_normalized_by_distinguished h beta, ?_⟩
  intro p hp
  exact ⟨fun X hXB hX hXnorm =>
    triple_invariant_subgroup_extends h S hzS hzcenter beta hbeta p hp X hXB hX hXnorm,
    triple_contains_pair_sylow_iff_motion h S hzS hzcenter beta hbeta p hp,
    triple_exact_motion_of_contains_pair_sylow h S hzS hzcenter beta hbeta p hp⟩

end CFSG.ProperTwoGeneratedCore
