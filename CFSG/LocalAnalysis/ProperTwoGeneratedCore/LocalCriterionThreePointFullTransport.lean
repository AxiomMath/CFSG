module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointMotion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointNormalizingFlip

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_full_pair_sylow_three_point_transport
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime)
    (hcontains : ∃ Q : Sylow p (pairPointStabilizer H beta),
      (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta) :
    let B := pairPointStabilizer H beta
    let E := triplePointStabilizer H z beta
    let F := oppositePairStabilizer H z beta
    let JB := pairOddCore H beta
    let JF := oppositePairOddCore H z beta
    let V := (CFSG.oddCore E).map E.subtype
    V = JB ⊓ E ∧ V = JF ⊓ E ∧
      (B : Set G) = (JB : Set G) * (E : Set G) ∧
      (F : Set G) = (JF : Set G) * (E : Set G) ∧
      Nat.card F = Nat.card B ∧
      (∃ P : Sylow p V,
        z ∈ Subgroup.normalizer (((P : Subgroup V).map V.subtype : Subgroup G) : Set G)) ∧
      ∀ P : Sylow p V,
        z ∈ Subgroup.normalizer (((P : Subgroup V).map V.subtype : Subgroup G) : Set G) →
        (∃ R : Sylow p JB,
          (R : Subgroup JB).map JB.subtype = (P : Subgroup V).map V.subtype) ∧
        (∃ R : Sylow p JF,
          (R : Subgroup JF).map JF.subtype = (P : Subgroup V).map V.subtype) ∧
        Nat.card (conjugacyWithin ((P : Subgroup V).map V.subtype) z) =
          p ^ (Nat.card (conjugacyWithin H z)).factorization p ∧
        ∃ t ∈ rightPairFlipFiber H z beta,
          rightCosetTranslate H beta t = rightCosetMk H 1 ∧
          t ∈ Subgroup.normalizer (((P : Subgroup V).map V.subtype : Subgroup G) : Set G) ∧
          let delta := rightCosetTranslate H (rightCosetTranslate H beta z) t
          delta ≠ rightCosetMk H 1 ∧
            rightConjugate F t = pairPointStabilizer H delta ∧
            ∃ R : Sylow p (rightConjugate F t),
              (R : Subgroup (rightConjugate F t)).map (rightConjugate F t).subtype ≤
                triplePointStabilizer H z delta := by
  dsimp only
  obtain ⟨t₀, ht₀⟩ := original_pair_flip_exists h beta hbeta
  refine ⟨triple_odd_core_eq_pair_intersection h S hzS hzcenter beta hbeta,
    triple_odd_core_eq_opposite_pair_intersection h S hzS hzcenter beta hbeta,
    pair_stabilizer_eq_odd_core_mul_triple h S hzS hzcenter hbeta ht₀,
    opposite_pair_eq_odd_core_mul_triple h S hzS hzcenter beta hbeta,
    opposite_pair_order_eq_pair h S hzS hzcenter beta hbeta,
    triple_odd_core_invariant_sylow_exists h beta p hp, ?_⟩
  intro P hzP
  obtain ⟨hPB, hPF⟩ := triple_odd_core_sylow_full_in_both_pairs
    h S hzS hzcenter beta hbeta p hp hcontains P
  have hmotion := triple_odd_core_invariant_sylow_motion
    h S hzS hzcenter beta hbeta p hp hcontains P hzP
  refine ⟨hPB, hPF, hmotion, ?_⟩
  obtain ⟨PB, hPBimage⟩ := hPB
  obtain ⟨t, ht, htP⟩ := pair_odd_core_sylow_normalizing_flip
    h S hzS hzcenter hbeta ht₀ p hp PB
  rw [hPBimage] at htP
  refine ⟨t, ht, right_pair_flip_returns h.distinguished_order ht, htP, ?_⟩
  let V : Subgroup G := (CFSG.oddCore (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  have hPopp : (P : Subgroup V).map V.subtype ≤ oppositePairStabilizer H z beta :=
    (Subgroup.map_subtype_le (P : Subgroup V)).trans
      ((Subgroup.map_subtype_le (CFSG.oddCore (triplePointStabilizer H z beta))).trans
      (triple_stabilizer_le_opposite_pair H z beta))
  have hPgroup : IsPGroup p ((P : Subgroup V).map V.subtype) :=
    P.isPGroup'.map V.subtype
  obtain ⟨hdelta, hpair, R, _, hRtriple⟩ :=
    full_motion_opposite_pair_flip_contains_triple_sylow
      h S hzS hzcenter hbeta ht p hp _ hPopp hzP htP hPgroup hmotion
  refine ⟨hdelta, hpair, ?_⟩
  rw [hpair]
  exact ⟨R, hRtriple⟩

end CFSG.ProperTwoGeneratedCore
