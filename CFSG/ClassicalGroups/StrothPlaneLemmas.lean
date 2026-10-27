module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.ClassicalGroups

theorem polar_eq_zero_of_mem_sup_span {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (D : Submodule K V) (hD : ∀ d ∈ D, Q d = 0) {f c c' : V}
    (hc : c ∈ D ⊔ K ∙ f) (hc' : c' ∈ D ⊔ K ∙ f) (hcD : c ∉ D) (hc'D : c' ∉ D)
    (hQc : Q c = 0) (hQc' : Q c' = 0) : QuadraticMap.polar Q c c' = 0 := by
  obtain ⟨d, hd, y, hy, rfl⟩ := Submodule.mem_sup.mp hc
  obtain ⟨d', hd', y', hy', rfl⟩ := Submodule.mem_sup.mp hc'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨a', rfl⟩ := Submodule.mem_span_singleton.mp hy'
  have ha : a ≠ 0 := by rintro rfl; exact hcD (by simpa using hd)
  have ha' : a' ≠ 0 := by rintro rfl; exact hc'D (by simpa using hd')
  set c := d + a • f
  set c' := d' + a' • f
  set e := a • d' - a' • d with he_def
  have he : e ∈ D := D.sub_mem (D.smul_mem a hd') (D.smul_mem a' hd)
  have hsplit : a • c' = a' • c + e := by
    simp only [c, c', e, smul_add, smul_smul, mul_comm a a']; abel
  have hce : QuadraticMap.polar Q c e = 0 := by
    have h0 : Q (a • c') = 0 := by rw [QuadraticMap.map_smul, hQc', smul_zero]
    have h1 : Q (a' • c + e) = Q (a' • c) + Q e + QuadraticMap.polar Q (a' • c) e := by
      simp only [QuadraticMap.polar]; abel
    rw [← hsplit, h0, QuadraticMap.map_smul, hQc, smul_zero, hD e he, zero_add, zero_add,
      QuadraticMap.polar_smul_left, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left ha'
  have : a • QuadraticMap.polar Q c c' = 0 := by
    rw [← QuadraticMap.polar_smul_right, hsplit, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hQc, hce]
    simp
  exact (smul_eq_zero.mp this).resolve_left ha

end CFSG.ClassicalGroups
