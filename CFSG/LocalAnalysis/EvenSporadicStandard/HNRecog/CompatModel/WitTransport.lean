module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Dict
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.WitModel

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.Section4

section Cert


theorem exists_vertex_in_Gx {G : Type} [Group G] {a z : G} (h : F5Std a z) {d y t : G}
    (hd : IsConj a d) (hy : y ∈ orb2A a d) (ht : t ∈ InvIn (Gxy y d)) (h1 : t ≠ d) (h2 : t ≠ y)
    (h3 : t ≠ y * d) :
    ∃ w : G, w ∈ Gxy d t ∧ IsConj a w ∧ w ∉ Gx y ∧ orderOf (y * w) ≠ 5 ∧
      (orderOf (y * w) = 4 → IsConj a ((y * w) ^ 2)) := by
  obtain ⟨hyd, Ψ, hΨ, hΨy⟩ := exists_vertexIso_at_pB h hd hy
  have hP := natCard_P1408_of_F5Std h
  have htd : t ∈ Gx d := (mem_Gxy.1 ht.1).2
  have hty : t ∈ Gx y := (mem_Gxy.1 ht.1).1
  have hdy : d * y = y * d := mem_Gx.1 hyd
  have hτo : orderOf (Ψ ⟨t, htd⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ht.2
  have hτc : pB * Ψ ⟨t, htd⟩ = Ψ ⟨t, htd⟩ * pB := by
    rw [← hΨy, ← map_mul, ← map_mul]
    exact congrArg Ψ (Subtype.ext (mem_Gx.1 hty))
  have hne1 : Ψ ⟨t, htd⟩ ≠ pA := fun e => h1 (by
    have : (⟨t, htd⟩ : ↥(Gx d)) = GxSelf d := Ψ.injective (e.trans hΨ.self_eq.symm)
    exact congrArg Subtype.val this)
  have hne2 : Ψ ⟨t, htd⟩ ≠ pB := fun e => h2 (by
    have : (⟨t, htd⟩ : ↥(Gx d)) = ⟨y, hyd⟩ := Ψ.injective (e.trans hΨy.symm)
    exact congrArg Subtype.val this)
  have hne3 : Ψ ⟨t, htd⟩ ≠ pA * pB := fun e => h3 (by
    have : (⟨t, htd⟩ : ↥(Gx d)) = GxSelf d * ⟨y, hyd⟩ :=
      Ψ.injective (by rw [map_mul, hΨ.self_eq, hΨy]; exact e)
    exact (congrArg Subtype.val this).trans hdy)
  obtain ⟨w, hw, hwc⟩ := exists_modelVertex hP hτo hτc hne1 hne2 hne3
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  have hΨw : Ψ (Ψ.symm w) = w := MulEquiv.apply_symm_apply Ψ w
  have hu : Ψ (⟨y, hyd⟩ * Ψ.symm w) = pB * w := by rw [map_mul, hΨy, hΨw]
  have hord : orderOf (y * (Ψ.symm w : G)) = orderOf (pB * w) := by
    have e1 := Subgroup.orderOf_coe (⟨y, hyd⟩ * Ψ.symm w : ↥(Gx d))
    have e2 := MulEquiv.orderOf_eq Ψ (⟨y, hyd⟩ * Ψ.symm w)
    rw [hu] at e2
    exact e1.trans e2.symm
  refine ⟨(Ψ.symm w : G), mem_Gxy.2 ⟨(Ψ.symm w).2, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [mem_Gx]
    have : (⟨t, htd⟩ : ↥(Gx d)) * Ψ.symm w = Ψ.symm w * ⟨t, htd⟩ :=
      Ψ.injective (by rw [map_mul, map_mul, hΨw]; exact hwc.symm)
    exact congrArg Subtype.val this
  · exact (hΨ.isConj_a_iff hd _).2 (by rw [hΨw]; exact hw1)
  · intro hc
    rw [mem_Gx] at hc
    apply hw2
    have : (⟨y, hyd⟩ : ↥(Gx d)) * Ψ.symm w = Ψ.symm w * ⟨y, hyd⟩ := Subtype.ext hc
    have := congrArg Ψ this
    rwa [map_mul, map_mul, hΨy, hΨw, eq_comm] at this
  · rw [hord]
    exact hw3
  · intro h4
    rw [hord] at h4
    have hsq : Ψ ((⟨y, hyd⟩ * Ψ.symm w) ^ 2) = (pB * w) ^ 2 := by rw [map_pow, hu]
    exact (hΨ.isConj_a_iff hd ((⟨y, hyd⟩ * Ψ.symm w) ^ 2)).2 (by rw [hsq]; exact hw4 h4)

end Cert

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
