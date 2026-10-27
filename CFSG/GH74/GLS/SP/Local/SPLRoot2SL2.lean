module

public import CFSG.GH74.GLS.SP.Local.SPLRoot1SL2

public section

namespace CFSG.GH74.GLS.SP.Local.SL2Root

open Subgroup CFSG.GH74.GLS.IVK.L2Torus CFSG.SL2MinimalFaithful

variable {F : Type*} [Field F]

@[expose] def negOffFun (M : SL2m F) : SL2m F :=
  sl2 (M.1 0 0) (-M.1 0 1) (-M.1 1 0) (M.1 1 1) (by linear_combination sl2_det M)

@[simp] theorem negOffFun_00 (M : SL2m F) : (negOffFun M).1 0 0 = M.1 0 0 := by
  simp [negOffFun]

@[simp] theorem negOffFun_01 (M : SL2m F) : (negOffFun M).1 0 1 = -M.1 0 1 := by
  simp [negOffFun]

@[simp] theorem negOffFun_10 (M : SL2m F) : (negOffFun M).1 1 0 = -M.1 1 0 := by
  simp [negOffFun]

@[simp] theorem negOffFun_11 (M : SL2m F) : (negOffFun M).1 1 1 = M.1 1 1 := by
  simp [negOffFun]

theorem negOffFun_mul (M N : SL2m F) : negOffFun (M * N) = negOffFun M * negOffFun N := by
  apply sl2_ext <;> simp [mul_apply'] <;> ring

theorem negOffFun_negOffFun (M : SL2m F) : negOffFun (negOffFun M) = M := by
  apply sl2_ext <;> simp

@[expose] def negOff (F : Type*) [Field F] : SL2m F ≃* SL2m F where
  toFun := negOffFun
  invFun := negOffFun
  left_inv := negOffFun_negOffFun
  right_inv := negOffFun_negOffFun
  map_mul' := negOffFun_mul

theorem negOff_negOff (M : SL2m F) : negOff F (negOff F M) = M := negOffFun_negOffFun M

theorem negOff_of_mem_diagSub {d : SL2m F} (hd : d ∈ diagSub F) : negOff F d = d := by
  obtain ⟨h1, h2⟩ := hd
  apply sl2_ext <;> simp [negOff, h1, h2]

theorem negOff_of_mem_upperSub {x : SL2m F} (hx : x ∈ upperSub F) : negOff F x = x⁻¹ := by
  obtain ⟨h0, h1, h2⟩ := hx
  apply sl2_ext <;>
    simp [negOff, inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11, h0, h1, h2]

theorem negOff_of_mem_lowerSub {x : SL2m F} (hx : x ∈ lowerSub F) : negOff F x = x⁻¹ := by
  obtain ⟨h0, h1, h2⟩ := hx
  apply sl2_ext <;>
    simp [negOff, inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11, h0, h1, h2]

theorem negOff_mul_w0 {s : SL2m F} (hs : s ∈ diagSub F) :
    negOff F (s * w0 F) = s * w0 F * (s * w0 F * (s * w0 F)) := by
  have h1 := w0_inv_diag hs
  have h2 : s * w0 F * (s * w0 F) = w0 F ^ 2 := by
    calc s * w0 F * (s * w0 F) = s * (w0 F * s * (w0 F)⁻¹) * (w0 F * w0 F) := by group
      _ = w0 F ^ 2 := by rw [h1]; simp [pow_two]
  obtain ⟨hs1, hs2⟩ := hs
  rw [h2]
  apply sl2_ext <;> simp [negOff, mul_apply', pow_two, w0, hs1, hs2]

@[simp] theorem dg_apply_01_zero (a b : F) (h : a * b = 1) : (dg a b h).1 0 1 = 0 := by simp [dg]

@[simp] theorem dg_apply_10_zero (a b : F) (h : a * b = 1) : (dg a b h).1 1 0 = 0 := by simp [dg]

theorem entry_10_eq_zero_of_conj_mem_upperSub {g : SL2m F}
    (hg : g * unipotent 1 * g⁻¹ ∈ upperSub F) : g.1 1 0 = 0 := by
  have h := hg.2.2
  rw [conj_unipotent_10] at h
  have : g.1 1 0 * g.1 1 0 = 0 := by linear_combination -h
  exact mul_self_eq_zero.1 this

theorem exists_upperSub_mul_diagSub {M : SL2m F} (hM : M.1 1 0 = 0) :
    ∃ u ∈ upperSub F, ∃ d ∈ diagSub F, M = u * d := by
  have hdet := sl2_det M
  rw [hM, mul_zero, sub_zero] at hdet
  refine ⟨M * (dg (M.1 0 0) (M.1 1 1) hdet)⁻¹, ?_, dg (M.1 0 0) (M.1 1 1) hdet,
    dg_mem_diagSub _ _ _, by group⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [mul_apply', inv_apply_00, inv_apply_10, dg_apply_10_zero, dg_apply_11]
    linear_combination hdet
  · simp only [mul_apply', inv_apply_01, inv_apply_11, dg_apply_00, dg_apply_01_zero]
    linear_combination hdet
  · simp only [mul_apply', inv_apply_00, inv_apply_10, dg_apply_10_zero, dg_apply_11]
    linear_combination M.1 1 1 * hM

theorem exists_bruhat_decomp {M : SL2m F} (hc : M.1 1 0 ≠ 0) :
    ∃ d ∈ diagSub F, M = unipotent (M.1 0 0 / M.1 1 0) * d * w0 F *
      unipotent (M.1 1 1 / M.1 1 0) := by
  have hdet := sl2_det M
  have hcc : (-(M.1 1 0)⁻¹) * (-M.1 1 0) = 1 := by field_simp
  refine ⟨dg (-(M.1 1 0)⁻¹) (-M.1 1 0) hcc, dg_mem_diagSub _ _ _, ?_⟩
  apply sl2_ext
  · simp [mul_apply', w0, dg_apply_00, dg_apply_11]
    field_simp
  · simp [mul_apply', w0, dg_apply_00, dg_apply_11]
    field_simp
    linear_combination -hdet
  · simp [mul_apply', w0, dg_apply_00, dg_apply_11]
  · simp [mul_apply', w0, dg_apply_00, dg_apply_11]
    field_simp

end CFSG.GH74.GLS.SP.Local.SL2Root
