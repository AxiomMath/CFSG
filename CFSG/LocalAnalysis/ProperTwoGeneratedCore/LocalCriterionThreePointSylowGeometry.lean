module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylowCounting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open scoped Pointwise

variable {G : Type*} [Group G]

theorem conjugacyWithin_mono {A B : Subgroup G} (hAB : A ≤ B) (t : G) :
    conjugacyWithin A t ⊆ conjugacyWithin B t := by
  rintro s ⟨a, has⟩
  exact ⟨⟨a, hAB a.property⟩, has⟩

theorem pair_flip_fiber_eq_stabilizer_class [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    rightPairFlipFiber H z beta = conjugacyWithin (pairPointStabilizer H beta) t := by
  apply Set.Subset.antisymm
  · rw [pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta ht]
    exact conjugacyWithin_mono (pairOddCore_le H beta t).1 t
  · intro s hs
    rw [pair_flip_fiber_eq_pair_class h S hzS hzcenter hbeta ht]
    exact conjugacyWithin_mono (pairPointStabilizer_le_pairFlipGroup H beta t) t hs

theorem pair_stabilizer_t_centralizer_index_eq_class_card [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    ((Subgroup.centralizer ({t} : Set G)).subgroupOf
      (pairPointStabilizer H beta)).index = Nat.card (conjugacyWithin H z) := by
  rw [← conjugacyWithin_card_eq_centralizer_index,
    ← pair_flip_fiber_eq_stabilizer_class h S hzS hzcenter hbeta ht]
  exact (involution_point_uniform_pair_flips h beta hbeta).1

theorem point_subgroup_eq_centralizer_mul_pair_stabilizer [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    (H : Set G) = (Subgroup.centralizer ({z} : Set G) : Set G) *
      (pairPointStabilizer H beta : Set G) := by
  have hfactor := point_subgroup_eq_centralizer_mul_inverted_set h S hzS hzcenter hbeta ht
  ext a
  constructor
  · intro ha
    rw [hfactor] at ha
    obtain ⟨c, hc, i, hi, hci⟩ := Set.mem_mul.mp ha
    exact Set.mem_mul.mpr ⟨c, hc, i, (pairOddCore_le H beta t).1 hi.1, hci⟩
  · intro ha
    obtain ⟨c, hc, b, hb, rfl⟩ := Set.mem_mul.mp ha
    exact H.mul_mem (point_centralizer_le h hc) (pairPointStabilizer_le_point H beta hb)

theorem point_subgroup_eq_pair_stabilizer_mul_centralizer [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    (H : Set G) = (pairPointStabilizer H beta : Set G) *
      (Subgroup.centralizer ({z} : Set G) : Set G) := by
  have hfactor := point_subgroup_eq_centralizer_mul_pair_stabilizer h S hzS hzcenter hbeta ht
  ext a
  constructor
  · intro ha
    have hainv : a⁻¹ ∈ (H : Set G) := H.inv_mem ha
    rw [hfactor] at hainv
    obtain ⟨c, hc, b, hb, hcb⟩ := Set.mem_mul.mp hainv
    refine Set.mem_mul.mpr ⟨b⁻¹, (pairPointStabilizer H beta).inv_mem hb,
      c⁻¹, (Subgroup.centralizer ({z} : Set G)).inv_mem hc, ?_⟩
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv hcb
  · intro ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.mp ha
    exact H.mul_mem (pairPointStabilizer_le_point H beta hb) (point_centralizer_le h hc)

theorem point_class_eq_pair_stabilizer_class [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    conjugacyWithin H z = conjugacyWithin (pairPointStabilizer H beta) z := by
  apply Set.Subset.antisymm
  · rintro s ⟨a, rfl⟩
    have ha : (a : G) ∈ (H : Set G) := a.property
    rw [point_subgroup_eq_centralizer_mul_pair_stabilizer h S hzS hzcenter hbeta ht] at ha
    obtain ⟨c, hc, b, hb, hcb⟩ := Set.mem_mul.mp ha
    have hcconj : c⁻¹ * z * c = z := by
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    refine ⟨⟨b, hb⟩, ?_⟩
    change b⁻¹ * z * b = (a : G)⁻¹ * z * a
    rw [← hcb, mul_inv_rev]
    calc
      b⁻¹ * z * b = b⁻¹ * (c⁻¹ * z * c) * b := by rw [hcconj]
      _ = b⁻¹ * c⁻¹ * z * (c * b) := by group
  · exact conjugacyWithin_mono (pairPointStabilizer_le_point H beta) z

theorem pair_stabilizer_z_centralizer_index_eq_class_card [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    ((Subgroup.centralizer ({z} : Set G)).subgroupOf
      (pairPointStabilizer H beta)).index = Nat.card (conjugacyWithin H z) := by
  rw [← conjugacyWithin_card_eq_centralizer_index,
    ← point_class_eq_pair_stabilizer_class h S hzS hzcenter hbeta ht]

theorem pair_subgroup_t_centralizer_eq (H : Subgroup G) (beta : rightCosetSpace H)
    (t : G) (ht : t ∈ pairFlipGroup H beta t) :
    (Subgroup.centralizer ({(⟨t, ht⟩ : pairFlipGroup H beta t)} :
      Set (pairFlipGroup H beta t))).subgroupOf
        ((pairPointStabilizer H beta).subgroupOf (pairFlipGroup H beta t)) =
      ((Subgroup.centralizer ({t} : Set G)).subgroupOf
        (pairFlipGroup H beta t)).subgroupOf
          ((pairPointStabilizer H beta).subgroupOf (pairFlipGroup H beta t)) := by
  ext b
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun hcomm => congrArg Subtype.val hcomm,
    fun hcomm => Subtype.ext hcomm⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
