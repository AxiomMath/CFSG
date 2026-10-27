module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G]

theorem original_involution_swap_reverse
    (H : Subgroup G) (a b : rightCosetSpace H) (s : G)
    (hs : orderOf s = 2) (hab : pointRightCosetMul H a s = b) :
    pointRightCosetMul H b s = a := by
  have hss : s * s = 1 := by simpa only [hs, pow_two] using pow_orderOf_eq_one s
  rw [← hab, pointRightCosetMul_mul, hss, pointRightCosetMul_one]

theorem original_pair_group_outside_iff_swaps
    {H : Subgroup G} {z t : G} (hz : orderOf z = 2)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (ht : t ∈ rightPairFlipFiber H z beta) (g : G) :
    (g ∈ pairFlipGroup H beta t ∧ g ∉ pairPointStabilizer H beta) ↔
      (pointRightCosetMul H (rightCosetMk H 1) g = beta ∧
        pointRightCosetMul H beta g = rightCosetMk H 1) := by
  let D := pairPointStabilizer H beta
  let K := pairFlipGroup H beta t
  let DK := D.subgroupOf K
  have htK : t ∈ K := flip_mem_pairFlipGroup H beta t
  have htD : t ∉ D := fun h => pair_flip_not_mem_point hbeta ht
    (pairPointStabilizer_le_point H beta h)
  have htorder := order_two_of_mem_pointClass hz ht.1
  have htt : t * t = 1 := by simpa only [htorder, pow_two] using pow_orderOf_eq_one t
  have hta : pointRightCosetMul H (rightCosetMk H 1) t = beta := by
    rw [pointRightCosetMul_eq_translate]
    exact ht.2
  have htb : pointRightCosetMul H beta t = rightCosetMk H 1 :=
    original_involution_swap_reverse H _ _ t htorder hta
  have hindex : DK.index = 2 := pair_group_index_two hz hbeta ht
  constructor
  · rintro ⟨hgK, hgD⟩
    have hgtD : g * t ∈ D := by
      have hiff := Subgroup.mul_mem_iff_of_index_two hindex
        (a := (⟨g, hgK⟩ : K)) (b := (⟨t, htK⟩ : K))
      have hgnot : (⟨g, hgK⟩ : K) ∉ DK := hgD
      have htnot : (⟨t, htK⟩ : K) ∉ DK := htD
      have hmem := hiff.mpr (by simp only [hgnot, htnot])
      exact hmem
    have hga : pointRightCosetMul H (rightCosetMk H 1) (g * t) = rightCosetMk H 1 :=
      (mem_point_right_stabilizer_iff H _ _).mp hgtD.1
    have hgb : pointRightCosetMul H beta (g * t) = beta :=
      (mem_point_right_stabilizer_iff H _ _).mp hgtD.2
    have hrecover : g = (g * t) * t := by simp only [mul_assoc, htt, mul_one]
    constructor
    · calc
        pointRightCosetMul H (rightCosetMk H 1) g =
            pointRightCosetMul H (pointRightCosetMul H (rightCosetMk H 1) (g * t)) t := by
          rw [pointRightCosetMul_mul, ← hrecover]
        _ = beta := by rw [hga, hta]
    · calc
        pointRightCosetMul H beta g =
            pointRightCosetMul H (pointRightCosetMul H beta (g * t)) t := by
          rw [pointRightCosetMul_mul, ← hrecover]
        _ = rightCosetMk H 1 := by rw [hgb, htb]
  · rintro ⟨hga, hgb⟩
    have hgtD : g * t ∈ D := by
      constructor
      · apply (mem_point_right_stabilizer_iff H _ _).mpr
        rw [← pointRightCosetMul_mul, hga, htb]
      · apply (mem_point_right_stabilizer_iff H _ _).mpr
        rw [← pointRightCosetMul_mul, hgb, hta]
    have hgK : g ∈ K := by
      have hprod := K.mul_mem
        (pairPointStabilizer_le_pairFlipGroup H beta t hgtD) htK
      simpa only [mul_assoc, htt, mul_one] using hprod
    refine ⟨hgK, ?_⟩
    intro hgD
    have hfix := (mem_point_right_stabilizer_iff H _ g).mp hgD.1
    exact hbeta (hga.symm.trans hfix)

theorem original_class_outside_eq_swap_fiber
    {H : Subgroup G} {z t : G} (hz : orderOf z = 2)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (ht : t ∈ rightPairFlipFiber H z beta) (s : G) (hs : orderOf s = 2) :
    involutionPointClass s ∩
        ((pairFlipGroup H beta t : Set G) \ (pairPointStabilizer H beta : Set G)) =
      {v | v ∈ involutionPointClass s ∧
        pointRightCosetMul H (rightCosetMk H 1) v = beta} := by
  ext v
  constructor
  · rintro ⟨hv, hvK, hvD⟩
    exact ⟨hv, ((original_pair_group_outside_iff_swaps hz beta hbeta ht v).mp
      ⟨hvK, hvD⟩).1⟩
  · rintro ⟨hv, hswap⟩
    exact ⟨hv, (original_pair_group_outside_iff_swaps hz beta hbeta ht v).mpr
      ⟨hswap, original_involution_swap_reverse H _ _ v
        (order_two_of_mem_pointClass hs hv) hswap⟩⟩

theorem distinguished_swap_fiber_eq_pair_stabilizer_class [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    rightPairFlipFiber H z beta = conjugacyWithin (pairPointStabilizer H beta) t := by
  ext s
  constructor
  · intro hs
    rw [pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta ht] at hs
    obtain ⟨j, hj⟩ := hs
    exact ⟨⟨j.val, (pairOddCore_le H beta t).1 j.property⟩, hj⟩
  · rintro ⟨d, hd⟩
    have hconj := pair_group_conjugate_flip_mem h.distinguished_order hbeta ht ht
      (pairPointStabilizer_le_pairFlipGroup H beta t d.property)
    change rightConjugateElem t (d : G) = s at hd
    exact hd ▸ hconj

theorem distinguished_class_outside_pair_group [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    involutionPointClass z ∩
        ((pairFlipGroup H beta t : Set G) \ (pairPointStabilizer H beta : Set G)) =
      conjugacyWithin (pairPointStabilizer H beta) t := by
  rw [original_class_outside_eq_swap_fiber h.distinguished_order beta hbeta ht
    z h.distinguished_order]
  simp only [pointRightCosetMul_eq_translate]
  change rightPairFlipFiber H z beta = _
  exact distinguished_swap_fiber_eq_pair_stabilizer_class h S hzS hzcenter beta hbeta t ht

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
