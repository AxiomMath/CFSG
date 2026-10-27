module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylowActions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowBridge

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

variable {G : Type*} [Group G]

theorem sylow_subtype_image_conjugation (p : ℕ) (Y : Subgroup G)
    (P : Sylow p Y) (a : Y) :
    ((a • P : Sylow p Y) : Subgroup Y).map Y.subtype =
      ((P : Subgroup Y).map Y.subtype).map (MulAut.conj (a : G)).toMonoidHom := by
  change ((P : Subgroup Y).map (MulAut.conj a).toMonoidHom).map Y.subtype = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem odd_subgroup_sylow_normalizing_involution_conjugate [Finite G]
    (p : ℕ) (hp : p.Prime) (Y : Subgroup G) (t : G) (ht : orderOf t = 2)
    (hYodd : Odd (Nat.card Y)) (hYnorm : t ∈ Subgroup.normalizer (Y : Set G))
    (P : Sylow p Y) :
    ∃ s ∈ conjugacyWithin Y t,
      s ∈ Subgroup.normalizer (((P : Subgroup Y).map Y.subtype : Subgroup G) : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQnorm⟩ := involution_normalized_odd_subgroup_invariant_sylow
    p hp Y t ht hYodd (Subgroup.zpowers_le.mpr hYnorm)
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq Y Q P
  let e := MulAut.conj (a : G)
  have hmap : ((Q : Subgroup Y).map Y.subtype).map e.toMonoidHom =
      (P : Subgroup Y).map Y.subtype := by
    rw [← sylow_subtype_image_conjugation, ha]
  have hnorm := Subgroup.mem_map_of_mem e.toMonoidHom hQnorm
  rw [Subgroup.map_normalizer_eq_of_bijective _ e.bijective, hmap] at hnorm
  refine ⟨rightConjugateElem t (a : G)⁻¹, ⟨a⁻¹, rfl⟩, ?_⟩
  simpa only [e, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    rightConjugateElem, inv_inv] using hnorm

theorem pair_flip_normalizes_ambient_odd_core [Finite G]
    {H : Subgroup G} {z : G} (hz : orderOf z = 2)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    t ∈ Subgroup.normalizer (pairOddCore H beta : Set G) := by
  let K := pairFlipGroup H beta t
  let J := (pairOddCore H beta).subgroupOf K
  let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  let : J.Normal := pairOddCore_normal_in_pair_group hz hbeta ht
  have hnormal : Subgroup.normalizer (J : Set K) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have htJ : tK ∈ Subgroup.normalizer (J : Set K) := by
    rw [hnormal]
    exact Subgroup.mem_top _
  have hnorm := (normalizer_in_subgroup_iff_ambient_image K J tK).mp htJ
  have hmap : J.map K.subtype = pairOddCore H beta :=
    Subgroup.map_subgroupOf_eq_of_le (pairOddCore_le H beta t).2.1
  rwa [hmap] at hnorm

theorem pair_odd_core_sylow_normalizing_flip [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (p : ℕ) (hp : p.Prime) (P : Sylow p (pairOddCore H beta)) :
    ∃ s ∈ rightPairFlipFiber H z beta,
      s ∈ Subgroup.normalizer
        (((P : Subgroup (pairOddCore H beta)).map
          (pairOddCore H beta).subtype : Subgroup G) : Set G) := by
  obtain ⟨s, hsclass, hsnorm⟩ := odd_subgroup_sylow_normalizing_involution_conjugate
    p hp (pairOddCore H beta) t
    (order_two_of_mem_pointClass h.distinguished_order ht.1)
    (pairOddCore_odd H beta)
    (pair_flip_normalizes_ambient_odd_core h.distinguished_order hbeta ht) P
  refine ⟨s, ?_, hsnorm⟩
  rwa [pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta ht]

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
