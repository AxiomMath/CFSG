module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_full_pair_odd_core_data
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    let D := pairPointStabilizer H beta
    let K := pairFlipGroup H beta t
    let J := oddCore K
    let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
    J ≤ D.subgroupOf K ∧ Odd (Nat.card J) ∧
      QuotientGroup.mk' J tK ∈ Subgroup.center (K ⧸ J) := by
  let D := pairPointStabilizer H beta
  let K := pairFlipGroup H beta t
  let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  let DK := D.subgroupOf K
  let : DK.Normal := pair_stabilizer_normal h.distinguished_order hbeta ht
  let JK := (pairOddCore H beta).subgroupOf K
  let : JK.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
  have hcenter : (QuotientGroup.mk tK : K ⧸ JK) ∈ Subgroup.center (K ⧸ JK) :=
    (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).1
  have hcore : oddCore K = JK :=
    pair_group_oddCore_subgroupOf_eq h.distinguished_order hbeta ht
  refine ⟨oddCore_le_index_two DK (pair_group_index_two h.distinguished_order hbeta ht),
    CFSG.ComponentClassification.OddCore.odd_card K, ?_⟩
  change (QuotientGroup.mk tK : K ⧸ oddCore K) ∈ Subgroup.center (K ⧸ oddCore K)
  apply Subgroup.mem_center_iff.mpr
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hcomm := Subgroup.mem_center_iff.mp hcenter (QuotientGroup.mk g : K ⧸ JK)
  have hmJK : (g * tK)⁻¹ * (tK * g) ∈ JK := by
    apply QuotientGroup.eq.mp
    simpa only [QuotientGroup.mk_mul] using hcomm
  have hm : (g * tK)⁻¹ * (tK * g) ∈ oddCore K := hcore ▸ hmJK
  have hq : (QuotientGroup.mk (g * tK) : K ⧸ oddCore K) =
      QuotientGroup.mk (tK * g) := QuotientGroup.eq.mpr hm
  simpa only [QuotientGroup.mk_mul] using hq

omit [Finite G] in
theorem original_pair_group_involution_data
    {H : Subgroup G} {z : G} (hz : orderOf z = 2)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2)
    (huD : u ∈ pairPointStabilizer H beta) (hut : Commute u t)
    (ht : t ∈ rightPairFlipFiber H z beta) :
    let D := pairPointStabilizer H beta
    let K := pairFlipGroup H beta t
    let uK : K := ⟨u, pairPointStabilizer_le_pairFlipGroup H beta t huD⟩
    let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
    IsInvolution uK ∧ IsInvolution tK ∧
      uK ∈ D.subgroupOf K ∧ tK ∉ D.subgroupOf K ∧ Commute uK tK := by
  let K := pairFlipGroup H beta t
  let uK : K := ⟨u, pairPointStabilizer_le_pairFlipGroup H beta t huD⟩
  let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  have huK : orderOf uK = 2 := (Subgroup.orderOf_coe uK).symm.trans hu
  have htK : orderOf tK = 2 := (Subgroup.orderOf_coe tK).symm.trans
    (order_two_of_mem_pointClass hz ht.1)
  refine ⟨?_, ?_, huD, ?_, ?_⟩
  · exact ⟨(orderOf_eq_prime_iff.mp huK).2, (orderOf_eq_prime_iff.mp huK).1⟩
  · exact ⟨(orderOf_eq_prime_iff.mp htK).2, (orderOf_eq_prime_iff.mp htK).1⟩
  · intro htD
    exact pair_flip_not_mem_point hbeta ht (pairPointStabilizer_le_point H beta htD)
  · apply Subtype.ext
    exact hut

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
