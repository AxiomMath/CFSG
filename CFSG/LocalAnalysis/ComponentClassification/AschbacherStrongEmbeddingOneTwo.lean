module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCounting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoData
public import CFSG.LocalAnalysis.ComponentClassification.OddIndexSylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTwoOne

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] {H : Subgroup G} {z : G}

theorem centralSylow_of_odd_class [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (hodd : Odd (Nat.card (conjugacyWithin H z))) : InvolutionPointCentralSylow z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := Subgroup.centralizer ({z} : Set G)
  have hCH : C ≤ H := centralizer_le_of_unique huniq
  have hindex : (C.subgroupOf H).index = Nat.card (conjugacyWithin H z) := by
    have h1 := (C.subgroupOf H).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv] at h1
    have h2 := conjugacyWithin_card_mul_centralizer (H := H) huniq
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  obtain ⟨T0⟩ : Nonempty (Sylow 2 C) := inferInstance
  obtain ⟨D, hD⟩ := OddIndexSylow.nested C H hCH (hindex ▸ hodd) T0
  let zC : C := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hzcenter : Subgroup.zpowers zC ≤ Subgroup.center C := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_center_iff.mpr fun c => Subtype.ext ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp c.property
  have hzorder : orderOf zC = 2 := by rw [← Subgroup.orderOf_coe]; exact hz
  have : (Subgroup.zpowers zC).Normal := Subgroup.normal_of_le_center hzcenter
  have hztwo : IsPGroup 2 (Subgroup.zpowers zC) := isPGroup_zpowers_of_orderOf_two hzorder
  have hzT0 : zC ∈ (T0 : Subgroup C) := hztwo.le_sylow_of_normal T0 (Subgroup.mem_zpowers zC)
  let T : Subgroup G := sylowImage H D
  have hT : T = (T0 : Subgroup C).map C.subtype := hD
  have hzT : z ∈ T := by rw [hT]; exact ⟨zC, hzT0, rfl⟩
  have hTC : T ≤ C := by rw [hT]; exact Subgroup.map_subtype_le _
  have hN : Subgroup.normalizer (T : Set G) ≤ H := by
    intro n hn
    apply (conj_mem_iff huniq n).mp
    have hn' := (Subgroup.normalizer (T : Set G)).inv_mem hn
    have hmem := (Subgroup.mem_normalizer_iff.mp hn' z).mp hzT
    simp only [inv_inv] at hmem
    exact hCH (hTC hmem)
  obtain ⟨P, hP⟩ := subgroup_sylow_ambient_of_normalizer_le H D hN
  have hzP : z ∈ (P : Subgroup G) := by rw [hP]; exact hzT
  refine ⟨P, hzP, Subgroup.mem_center_iff.mpr fun p => Subtype.ext ?_⟩
  have hpC : (p : G) ∈ C := hTC (hP.le p.property)
  exact Subgroup.mem_centralizer_singleton_iff.mp hpC

theorem centralProductCentralizer_of_productUniqueContainment [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (hH : H ≠ ⊤)
    (h1 : ProductUniqueContainment H z) : CentralProductCentralizer H z := by
  refine ⟨centralSylow_of_odd_class hz huniq (conjugacyWithin_card_odd hz huniq hH h1), ?_⟩
  intro t ht hzt hne c hc
  have hzH := mem_of_unique huniq
  have htH : t ∈ H := centralizer_le_of_unique huniq
    (Subgroup.mem_centralizer_singleton_iff.mpr hzt.eq.symm)
  apply (h1 t ht hzt hne c).mp
  have hfix : c⁻¹ * (z * t) * c = z * t := by
    rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hc, inv_mul_cancel_left]
  rw [hfix]
  exact H.mul_mem hzH htH

end CFSG.ComponentClassification.AschbacherStrongEmbedding
