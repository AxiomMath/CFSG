module

public import CFSG.Certificates.Kernel.Misc.F7MatSound

public section

namespace CFSG.KC.Misc.F7

open Finset

@[expose] def Echelon (V : Matrix (Fin 8) (Fin 45) (ZMod 7)) (p : Fin 8 → Fin 45) : Prop :=
  Pivots V p ∧ StrictMono p ∧ ∀ c (j : Fin 45), j < p c → V c j = 0

theorem Pivots.apply {V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {p : Fin 8 → Fin 45}
    (h : Pivots V p) (c c' : Fin 8) : rows V c' (p c) = if c' = c then 1 else 0 := by
  have hli := linearIndependent_of_pivots h
  have hmem : rows V c' ∈ rowSpan V := Submodule.subset_span (Set.mem_range_self c')
  have hs := (mem_rowSpan_iff h _).1 hmem
  have h2 : ∑ d, (rows V c' (p d) - if c' = d then 1 else 0) • rows V d = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← hs, sub_self]
  exact sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 hli) _ h2 c)

theorem exists_lead {V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {p : Fin 8 → Fin 45}
    (hV : Echelon V p) {u : Fin 45 → ZMod 7} (hu : u ∈ rowSpan V) (hne : u ≠ 0) :
    ∃ c, u (p c) ≠ 0 ∧ ∀ j, j < p c → u j = 0 := by
  classical
  obtain ⟨hp, hmono, hz⟩ := hV
  have hsum := (mem_rowSpan_iff hp u).1 hu
  have hS : (univ.filter fun c => u (p c) ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    apply hne
    rw [hsum]
    refine Finset.sum_eq_zero fun c _ => ?_
    have : u (p c) = 0 := by simpa using h (Finset.mem_univ c)
    rw [this, zero_smul]
  set c0 := (univ.filter fun c => u (p c) ≠ 0).min' hS
  have hc0 : u (p c0) ≠ 0 := (Finset.mem_filter.1 (Finset.min'_mem _ hS)).2
  refine ⟨c0, hc0, fun j hj => ?_⟩
  rw [hsum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : u (p c) = 0
  · rw [hc, zero_smul, Pi.zero_apply]
  · have hle : c0 ≤ c := Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ c, hc⟩)
    have hj' : j < p c := lt_of_lt_of_le hj (hmono.monotone hle)
    rw [Pi.smul_apply, smul_eq_mul]
    change u (p c) * V c j = 0
    rw [hz c j hj', mul_zero]

theorem pivot_mem {V V' : Matrix (Fin 8) (Fin 45) (ZMod 7)} {p p' : Fin 8 → Fin 45}
    (h : Echelon V p) (h' : Echelon V' p') (e : rowSpan V' ≤ rowSpan V) (d : Fin 8) :
    ∃ c, p c = p' d := by
  obtain ⟨hp', -, hz'⟩ := h'
  have hu : rows V' d ∈ rowSpan V := e (Submodule.subset_span (Set.mem_range_self d))
  have h1 : rows V' d (p' d) = 1 := by rw [hp'.apply d d, if_pos rfl]
  have hne : rows V' d ≠ 0 := fun h0 => by
    rw [h0, Pi.zero_apply] at h1
    exact zero_ne_one h1
  obtain ⟨c, hc, hzc⟩ := exists_lead h hu hne
  refine ⟨c, ?_⟩
  rcases lt_trichotomy (p c) (p' d) with hlt | heq | hgt
  · exact absurd (hz' d _ hlt) hc
  · exact heq
  · exact absurd (hzc _ hgt) (by rw [h1]; exact one_ne_zero)

theorem echelon_unique {V V' : Matrix (Fin 8) (Fin 45) (ZMod 7)} {p p' : Fin 8 → Fin 45}
    (h : Echelon V p) (h' : Echelon V' p') (e : rowSpan V = rowSpan V') : V = V' := by
  have hrange : Set.range p = Set.range p' := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨d, hd⟩ := pivot_mem h' h e.le c
      exact ⟨d, hd⟩
    · rintro ⟨d, rfl⟩
      obtain ⟨c, hc⟩ := pivot_mem h h' e.ge d
      exact ⟨c, hc⟩
  have hpp : p = p' := (StrictMono.range_inj_of_wellFoundedLT h.2.1 h'.2.1).1 hrange
  subst hpp
  ext d j
  have hu : rows V' d ∈ rowSpan V := e ▸ Submodule.subset_span (Set.mem_range_self d)
  have hsum := (mem_rowSpan_iff h.1 _).1 hu
  have hcoef : ∀ c, rows V' d (p c) = if d = c then 1 else 0 := fun c => h'.1.apply c d
  have : rows V' d = rows V d := by
    rw [hsum]
    simp only [hcoef, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  exact (congrFun this j).symm

end CFSG.KC.Misc.F7

end
