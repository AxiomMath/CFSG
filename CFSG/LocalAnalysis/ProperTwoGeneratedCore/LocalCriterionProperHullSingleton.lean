module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullTripleReduction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

universe u

variable {G : Type u} [Group G]

theorem properHull_global_point_class_mem {H : Subgroup G} {z w : G}
    (hzH : z ∈ H) (hw : w ∈ conjugacyWithin H z) :
    w ∈ H ∧ w ∈ involutionPointClass z := by
  obtain ⟨h, rfl⟩ := hw
  exact ⟨H.mul_mem (H.mul_mem (H.inv_mem h.property) hzH) h.property,
    ⟨(h : G), rfl⟩⟩

variable [Finite G]

theorem properHull_rank_one_global_class_singleton_of_point_centralizer
    {H Y : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : twoRank (properHull Y z) ≤ 1)
    (hpoint : H ⊓ Y ≤ Subgroup.centralizer ({z} : Set G)) :
    conjugacyWithin H z ∩ (Y : Set G) = {z} := by
  ext w
  constructor
  · rintro ⟨hwclass, hwY⟩
    obtain ⟨hwH, hwglobal⟩ := properHull_global_point_class_mem h.distinguished_mem hwclass
    have hcomm : Commute z w :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hpoint ⟨hwH, hwY⟩)).symm
    have hwz : w = z := by
      by_contra hne
      have htwo := local_involution_hull_two_rank_of_commuting_class
        h Y hzY hescape hwY hwglobal hcomm hne
      rw [← properHull_rank_eq_internal Y hzY] at htwo
      omega
    exact Set.mem_singleton_iff.mpr hwz
  · intro hw
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact ⟨⟨1, by simp⟩, hzY⟩

theorem properHull_rank_one_global_class_singleton_of_triple
    {H Y : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (htriple : distinguishedTripleCentralization H z)
    (hY : Y < ⊤) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : twoRank (properHull Y z) ≤ 1) :
    conjugacyWithin H z ∩ (Y : Set G) = {z} := by
  apply properHull_rank_one_global_class_singleton_of_point_centralizer
    h.local_datum hzY hescape hrank
  rw [properHull_rank_one_point_eq_centralizer_of_triple h htriple hY hzY hescape hrank]
  exact inf_le_right

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
