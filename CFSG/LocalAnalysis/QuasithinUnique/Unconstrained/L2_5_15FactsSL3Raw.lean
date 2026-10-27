module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3Inputs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.QuasithinUnique.Unc25K1

open scoped MatrixGroups

theorem rr_mul (x y : S3) : rr (x * y) = rmul (rr x) (rr y) := by
  simp [rr, rmul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem rr_inj : Function.Injective rr := by
  intro x y h
  simp only [rr, R9.mk.injEq] at h
  obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := h
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem rr_one : rr 1 = rone := by
  simp [rr, rone]

theorem mem_rawAll (r : R9) : r ∈ rawAll := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := r
  have hv : ∀ z : ZMod 3, z ∈ vals := by decide
  simp only [rawAll, List.mem_flatMap, List.mem_map]
  exact ⟨a, hv a, b, hv b, c, hv c, d, hv d, e, hv e, f, hv f, g, hv g, h, hv h, i, hv i, rfl⟩

theorem rr_det (x : S3) : rdet (rr x) = 1 := by
  have h : (x.1).det = 1 := x.2
  rw [Matrix.det_fin_three] at h
  simp only [rdet, rr]
  linear_combination h

theorem rr_mem (x : S3) : rr x ∈ rawList := by
  unfold rawList
  rw [List.mem_filter]
  exact ⟨mem_rawAll _, by simp [rr_det]⟩

theorem det_of_mem_rawList {r : R9} (h : r ∈ rawList) : rdet r = 1 := by
  unfold rawList at h
  rw [List.mem_filter] at h
  simpa using h.2

def ofR9 (r : R9) (h : rdet r = 1) : S3 :=
  ⟨!![r.a, r.b, r.c; r.d, r.e, r.f; r.g, r.h, r.i], by
    rw [Matrix.det_fin_three]
    simp only [rdet] at h
    simp
    linear_combination h⟩

theorem rr_ofR9 (r : R9) (h : rdet r = 1) : rr (ofR9 r h) = r := by
  obtain ⟨a, b, c, d, e, f, g, h', i⟩ := r
  simp [rr, ofR9]

theorem rr_comm_iff (x y : S3) : x * y = y * x ↔ rmul (rr x) (rr y) = rmul (rr y) (rr x) := by
  rw [← rr_mul, ← rr_mul]
  exact ⟨fun h => congrArg rr h, fun h => rr_inj h⟩

theorem rr_cube_iff (x : S3) : x ^ 3 = 1 ↔ rmul (rr x) (rmul (rr x) (rr x)) = rone := by
  rw [← rr_mul, ← rr_mul, ← rr_one]
  have : x ^ 3 = x * (x * x) := by simp [pow_succ, mul_assoc]
  rw [this]
  exact ⟨fun h => congrArg rr h, fun h => rr_inj h⟩

theorem rr_eq_one_iff (x : S3) : x = 1 ↔ rr x = rone := by
  rw [← rr_one]
  exact ⟨fun h => by rw [h], fun h => rr_inj h⟩

theorem rr_eq_iff (x y : S3) : x = y ↔ rr x = rr y :=
  ⟨fun h => by rw [h], fun h => rr_inj h⟩

end CFSG.QuasithinUnique.Unc25K1
