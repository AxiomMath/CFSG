module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointInvariantCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthHypotheses

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open scoped Pointwise

variable {G : Type*} [Group G]

theorem conjugacyWithin_eq_of_centralizer_product (F J : Subgroup G) (z : G)
    (hJF : J ≤ F)
    (hfactor : (F : Set G) = (F ⊓ Subgroup.centralizer ({z} : Set G) : Set G) * (J : Set G)) :
    conjugacyWithin F z = conjugacyWithin J z := by
  apply Set.Subset.antisymm
  · rintro s ⟨a, rfl⟩
    have ha : (a : G) ∈ (F : Set G) := a.property
    rw [hfactor] at ha
    obtain ⟨c, hc, j, hj, hcj⟩ := Set.mem_mul.mp ha
    have hcfix : c⁻¹ * z * c = z := by
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hc.2
      rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    refine ⟨⟨j, hj⟩, ?_⟩
    change j⁻¹ * z * j = (a : G)⁻¹ * z * a
    rw [← hcj, mul_inv_rev]
    calc
      j⁻¹ * z * j = j⁻¹ * (c⁻¹ * z * c) * j := by rw [hcfix]
      _ = j⁻¹ * c⁻¹ * z * (c * j) := by group
  · exact conjugacyWithin_mono hJF z

theorem opposite_pair_normalized_by_distinguished
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) :
    z ∈ Subgroup.normalizer (oppositePairStabilizer H z beta : Set G) := by
  have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two h.distinguished_order
  have hzz : z * z = 1 := by
    have hzpow := pow_orderOf_eq_one z
    rwa [h.distinguished_order, pow_two] at hzpow
  have hreturn : rightCosetTranslate H (rightCosetTranslate H beta z) z = beta := by
    rw [rightCosetTranslate_mul, hzz, rightCosetTranslate_one]
  have hconj (x : G) (hx : x ∈ oppositePairStabilizer H z beta) :
      z * x * z⁻¹ ∈ oppositePairStabilizer H z beta := by
    have hb := (mem_rightCosetStabilizer_iff H beta x).mp hx.1
    have hg := (mem_rightCosetStabilizer_iff H (rightCosetTranslate H beta z) x).mp hx.2
    constructor
    · apply (mem_rightCosetStabilizer_iff H beta _).mpr
      rw [hzinv, ← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hg, hreturn]
    · apply (mem_rightCosetStabilizer_iff H (rightCosetTranslate H beta z) _).mpr
      rw [hzinv, ← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hreturn, hb]
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  refine ⟨hconj x, fun hx => ?_⟩
  have htwice : z * (z * x * z⁻¹) * z⁻¹ = x := by
    rw [hzinv]
    calc
      z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hzz, one_mul, mul_one]
  simpa only [htwice] using hconj _ hx

theorem opposite_pair_odd_core_odd_and_normalized [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) :
    Odd (Nat.card (oppositePairOddCore H z beta)) ∧
      z ∈ Subgroup.normalizer (oppositePairOddCore H z beta : Set G) := by
  constructor
  · change Odd (Nat.card ((CFSG.oddCore (oppositePairStabilizer H z beta)).map
      (oppositePairStabilizer H z beta).subtype))
    rw [Subgroup.card_subtype]
    exact CFSG.ComponentClassification.OddCore.odd_card _
  · exact (generatedPairGrowth_normalizer_le_characteristic_image
      (oppositePairStabilizer H z beta) (CFSG.oddCore (oppositePairStabilizer H z beta))
      (CFSG.ComponentClassification.OddCore.characteristic _))
      (opposite_pair_normalized_by_distinguished h beta)

theorem opposite_pair_odd_core_class_card [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    Nat.card (conjugacyWithin (oppositePairOddCore H z beta) z) =
      Nat.card (conjugacyWithin H z) := by
  rw [← conjugacyWithin_eq_of_centralizer_product
    (oppositePairStabilizer H z beta) (oppositePairOddCore H z beta) z
    (Subgroup.map_subtype_le _)
    (opposite_pair_eq_z_centralizer_mul_odd_core h S hzS hzcenter beta hbeta)]
  exact opposite_pair_flip_class_card h S hzS hzcenter beta hbeta

theorem odd_invariant_sylow_motion [Finite G]
    (p : ℕ) (hp : p.Prime) (Y : Subgroup G) (z : G) (hz : orderOf z = 2)
    (hYodd : Odd (Nat.card Y)) (hYnorm : z ∈ Subgroup.normalizer (Y : Set G))
    (P : Sylow p Y)
    (hPnorm : z ∈ Subgroup.normalizer (((P : Subgroup Y).map Y.subtype : Subgroup G) : Set G)) :
    Nat.card (conjugacyWithin ((P : Subgroup Y).map Y.subtype) z) =
      p ^ (Nat.card (conjugacyWithin Y z)).factorization p := by
  obtain ⟨R, hR⟩ := involution_normalized_odd_sylow_fixed_intersection p hp Y z hz
    hYodd (Subgroup.zpowers_le.mpr hYnorm) P hPnorm
  rw [conjugacyWithin_card_eq_centralizer_index, conjugacyWithin_card_eq_centralizer_index]
  exact sylow_fixed_intersection_relIndex_prime_part p hp Y z P R hR

theorem triple_odd_core_invariant_sylow_exists [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (p : ℕ) (hp : p.Prime) :
    let V := (CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    ∃ P : Sylow p V, z ∈ Subgroup.normalizer (((P : Subgroup V).map V.subtype : Subgroup G) : Set G) := by
  dsimp only
  apply involution_normalized_odd_subgroup_invariant_sylow p hp _ z h.distinguished_order
  · rw [Subgroup.card_subtype]
    exact CFSG.ComponentClassification.OddCore.odd_card _
  · exact Subgroup.zpowers_le.mpr (generatedPairGrowth_distinguished_normalizes_triple_odd_core h beta)

theorem triple_odd_core_invariant_sylow_motion [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime)
    (hcontains : ∃ Q : Sylow p (pairPointStabilizer H beta),
      (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta)
    (P : Sylow p ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype))
    (hPnorm : z ∈ Subgroup.normalizer
      (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
        ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G)) :
    Nat.card (conjugacyWithin
      ((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
        ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype).subtype) z) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  obtain ⟨_, R, hR⟩ := triple_odd_core_sylow_full_in_both_pairs h S hzS hzcenter beta hbeta p hp hcontains P
  obtain ⟨hJodd, hJnorm⟩ := opposite_pair_odd_core_odd_and_normalized h beta
  rw [← hR] at hPnorm ⊢
  have hm := odd_invariant_sylow_motion p hp (oppositePairOddCore H z beta) z
    h.distinguished_order hJodd hJnorm R hPnorm
  rw [opposite_pair_odd_core_class_card h S hzS hzcenter beta hbeta] at hm
  exact hm

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
