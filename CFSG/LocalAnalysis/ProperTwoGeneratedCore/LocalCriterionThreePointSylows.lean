module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowBridge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylowIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointOddCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem pair_stabilizer_invariant_sylow_exists
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) (p : ℕ) (hp : p.Prime) :
    ∃ P : Sylow p (pairPointStabilizer H beta),
      t ∈ Subgroup.normalizer
        (((P : Subgroup (pairPointStabilizer H beta)).map
          (pairPointStabilizer H beta).subtype : Subgroup G) : Set G) := by
  let B := pairPointStabilizer H beta
  let K := pairFlipGroup H beta t
  let BK := B.subgroupOf K
  let J := (pairOddCore H beta).subgroupOf K
  let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  let : BK.Normal := pair_stabilizer_normal h.distinguished_order hbeta ht
  let : J.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
  have hcentral : QuotientGroup.mk' J tK ∈ Subgroup.center (K ⧸ J) :=
    (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).1
  obtain ⟨Q, hQ⟩ := odd_central_quotient_invariant_sylow_exists p hp BK J tK
    (pair_flip_restriction_order_two h.distinguished_order ht)
    (pair_odd_core_restriction_odd H beta t)
    (pair_odd_core_restriction_le_stabilizer H beta t) hcentral
  obtain ⟨P, hP⟩ := sylow_subgroupOf_extension_ambient_image p hp B K
    (pairPointStabilizer_le_pairFlipGroup H beta t) Q
  refine ⟨P, ?_⟩
  rw [hP]
  exact (normalizer_in_subgroup_iff_ambient_image K
    ((Q : Subgroup BK).map BK.subtype) tK).mp hQ

theorem pair_invariant_sylow_flip_class_card
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) (p : ℕ) (hp : p.Prime)
    (P : Sylow p (pairPointStabilizer H beta))
    (hPnorm : t ∈ Subgroup.normalizer
      (((P : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype : Subgroup G) : Set G)) :
    Nat.card (conjugacyWithin
      ((P : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype) t) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  let B := pairPointStabilizer H beta
  let K := pairFlipGroup H beta t
  let BK := B.subgroupOf K
  let J := (pairOddCore H beta).subgroupOf K
  let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  let : J.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
  have hcentral : QuotientGroup.mk' J tK ∈ Subgroup.center (K ⧸ J) :=
    (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).1
  obtain ⟨Q, hQ⟩ := sylow_subgroupOf_restriction_ambient_image p hp B K
    (pairPointStabilizer_le_pairFlipGroup H beta t) P
  have hQnorm : tK ∈ Subgroup.normalizer
      (((Q : Subgroup BK).map BK.subtype : Subgroup K) : Set K) := by
    apply (normalizer_in_subgroup_iff_ambient_image K _ tK).mpr
    change t ∈ Subgroup.normalizer
      ((((Q : Subgroup BK).map BK.subtype).map K.subtype : Subgroup G) : Set G)
    rw [hQ]
    exact hPnorm
  have hindex := odd_central_quotient_invariant_sylow_index p hp BK J tK
    (pair_flip_restriction_order_two h.distinguished_order ht)
    (pair_odd_core_restriction_odd H beta t)
    (pair_odd_core_restriction_le_stabilizer H beta t) hcentral Q hQnorm
  rw [pair_restricted_t_centralizer_index_eq_class_card h S hzS hzcenter hbeta ht] at hindex
  rw [← hQ]
  exact (conjugacyWithin_ambient_image_card_eq_internal_relIndex K
    ((Q : Subgroup BK).map BK.subtype) tK).trans hindex

theorem involution_point_sylow_flips_and_three_point_odd_core
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    (∀ p : ℕ, p.Prime →
      (∃ P : Sylow p (pairPointStabilizer H beta),
        t ∈ Subgroup.normalizer
          (((P : Subgroup (pairPointStabilizer H beta)).map
            (pairPointStabilizer H beta).subtype : Subgroup G) : Set G)) ∧
      ∀ P : Sylow p (pairPointStabilizer H beta),
        t ∈ Subgroup.normalizer
          (((P : Subgroup (pairPointStabilizer H beta)).map
            (pairPointStabilizer H beta).subtype : Subgroup G) : Set G) →
        Nat.card (conjugacyWithin
          ((P : Subgroup (pairPointStabilizer H beta)).map
            (pairPointStabilizer H beta).subtype) t) =
          p ^ (Nat.card (conjugacyWithin H z)).factorization p) ∧
    beta ≠ rightCosetMk H 1 ∧
    rightCosetTranslate H beta z ≠ beta ∧
    rightCosetTranslate H beta z ≠ rightCosetMk H 1 ∧
    (pairPointStabilizer H beta : Set G) =
      (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) : Set G) *
        (pairOddCore H beta : Set G) ∧
    (pairPointStabilizer H beta : Set G) =
      (pairOddCore H beta : Set G) * (triplePointStabilizer H z beta : Set G) ∧
    (oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype ≤ pairOddCore H beta := by
  refine ⟨?_, involution_point_three_point_odd_core h S hzS hzcenter beta hbeta t ht⟩
  intro p hp
  exact ⟨pair_stabilizer_invariant_sylow_exists h S hzS hzcenter hbeta ht p hp,
    pair_invariant_sylow_flip_class_card h S hzS hzcenter hbeta ht p hp⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
