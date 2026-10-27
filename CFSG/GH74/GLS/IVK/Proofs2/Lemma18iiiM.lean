module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open scoped MatrixGroups

namespace Lemma18iii

variable {F : Type} [Field F]

theorem conj_traces_trace_det_eq {h M N : Matrix (Fin 2) (Fin 2) F} (hh : h.det ≠ 0)
    (e : M * h = h * N) : M.trace = N.trace ∧ M.det = N.det := by
  have hu : IsUnit h.det := isUnit_iff_ne_zero.2 hh
  constructor
  · have hM : M = h * N * h⁻¹ := by
      calc M = M * (h * h⁻¹) := by rw [Matrix.mul_nonsing_inv h hu, mul_one]
        _ = (M * h) * h⁻¹ := by rw [mul_assoc]
        _ = h * N * h⁻¹ := by rw [e]
    rw [hM, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul h hu, one_mul]
  · have hd := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_mul] at hd
    exact mul_left_cancel₀ hh ((mul_comm _ _).trans hd)

theorem conj_traces_exists_intertwiner {M : Matrix (Fin 2) (Fin 2) F} (hM : M.det = 1)
    (hY : M.trace ^ 2 ≠ 4) :
    ∃ h : Matrix (Fin 2) (Fin 2) F, h.det ≠ 0 ∧ M * h = h * !![0, -1; 1, M.trace] := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : F, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  simp only [Matrix.det_fin_two_of, Matrix.trace_fin_two_of] at hM hY ⊢
  have key : ∃ x y : F, x * (c * x + d * y) - (a * x + b * y) * y ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ x y : F, x * (c * x + d * y) - (a * x + b * y) * y = 0 := fun x y => by
      by_contra hne
      exact hcon ⟨x, y, hne⟩
    have h1 := hcon' 1 0
    have h2 := hcon' 0 1
    have h3 := hcon' 1 1
    have hc : c = 0 := by linear_combination h1
    have hb : b = 0 := by linear_combination -h2
    have hda : d = a := by linear_combination h3 - h1 - h2
    subst hc hb hda
    exact hY (by linear_combination 4 * hM)
  obtain ⟨x, y, hxy⟩ := key
  refine ⟨!![x, a * x + b * y; y, c * x + d * y], ?_, ?_⟩
  · simpa [Matrix.det_fin_two_of] using hxy
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination (-x) * hM | linear_combination (-y) * hM

end Lemma18iii

theorem exists_conj_traces {F : Type} [Field F] (Y : SL(2, F))
    (hY : (Y : Matrix (Fin 2) (Fin 2) F).trace ^ 2 ≠ 4) (s : F) :
    ∃ g : SL(2, F),
      ((Y * (g * Y * g⁻¹) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
          (Y : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 2 - s ^ 2 ∧
      ((Y : Matrix (Fin 2) (Fin 2) F) * ((g * Y * g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) -
        ((g * Y * g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
          (Y : Matrix (Fin 2) (Fin 2) F)).det =
          s ^ 2 * ((Y : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 - s ^ 2) := by
  obtain ⟨h, hdet, hYh⟩ := Lemma18iii.conj_traces_exists_intertwiner Y.det_coe hY
  have hu : IsUnit h.det := isUnit_iff_ne_zero.2 hdet
  generalize (Y : Matrix (Fin 2) (Fin 2) F).trace = t at hYh hY ⊢
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin 2) (Fin 2) F, C = !![0, -1; 1, t] := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin 2) (Fin 2) F, U = !![1, s; 0, 1] := ⟨_, rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U' : Matrix (Fin 2) (Fin 2) F, U' = !![1, -s; 0, 1] := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin 2) (Fin 2) F, B' = !![s, s * t - s ^ 2 - 1; 1, t - s] :=
    ⟨_, rfl⟩
  rw [← hC] at hYh
  have hUU' : U * U' = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hU, hU', Matrix.mul_apply, Fin.sum_univ_two]
  have hUCU' : U * C * U' = B' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hU, hU', hC, hB', Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring
  have hGdet : (h * U * h⁻¹).det = 1 := by
    rw [Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det h).2 hu)]
    simp [hU, Matrix.det_fin_two_of]
  obtain ⟨g, hg⟩ : ∃ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) = h * U * h⁻¹ :=
    ⟨⟨_, hGdet⟩, rfl⟩
  have hgh : (g : Matrix (Fin 2) (Fin 2) F) * h = h * U := by
    rw [hg, mul_assoc, mul_assoc, Matrix.nonsing_inv_mul h hu, mul_one]
  have hginv : ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * h = h * U' := by
    have h1 : ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
        1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * h
        = ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (h * (U * U')) := by
          rw [hUU', mul_one]
      _ = ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
            ((g : Matrix (Fin 2) (Fin 2) F) * h) * U' := by
          rw [hgh]; simp only [mul_assoc]
      _ = h * U' := by
          rw [← mul_assoc _ (g : Matrix (Fin 2) (Fin 2) F), h1, one_mul]
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Fin 2) (Fin 2) F,
      B = ((g * Y * g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := ⟨_, rfl⟩
  have hB : B * h = h * B' := by
    rw [hBdef, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    calc (g : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) *
          ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * h
        = (g : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) * (h * U') := by
          rw [mul_assoc _ ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F), hginv]
      _ = (g : Matrix (Fin 2) (Fin 2) F) * ((Y : Matrix (Fin 2) (Fin 2) F) * h) * U' := by
          simp only [mul_assoc]
      _ = ((g : Matrix (Fin 2) (Fin 2) F) * h) * C * U' := by rw [hYh]; simp only [mul_assoc]
      _ = h * (U * C * U') := by rw [hgh]; simp only [mul_assoc]
      _ = h * B' := by rw [hUCU']
  have hYB : ((Y : Matrix (Fin 2) (Fin 2) F) * B) * h = h * (C * B') := by
    calc ((Y : Matrix (Fin 2) (Fin 2) F) * B) * h
        = (Y : Matrix (Fin 2) (Fin 2) F) * (B * h) := by rw [mul_assoc]
      _ = ((Y : Matrix (Fin 2) (Fin 2) F) * h) * B' := by rw [hB, ← mul_assoc]
      _ = h * (C * B') := by rw [hYh, mul_assoc]
  have hBY : (B * (Y : Matrix (Fin 2) (Fin 2) F)) * h = h * (B' * C) := by
    calc (B * (Y : Matrix (Fin 2) (Fin 2) F)) * h
        = B * ((Y : Matrix (Fin 2) (Fin 2) F) * h) := by rw [mul_assoc]
      _ = (B * h) * C := by rw [hYh, ← mul_assoc]
      _ = h * (B' * C) := by rw [hB, mul_assoc]
  refine ⟨g, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← hBdef,
      (Lemma18iii.conj_traces_trace_det_eq hdet hYB).1]
    simp [hC, hB', Matrix.trace_fin_two]
    ring
  · rw [← hBdef]
    have hcomm : ((Y : Matrix (Fin 2) (Fin 2) F) * B - B * (Y : Matrix (Fin 2) (Fin 2) F)) * h =
        h * (C * B' - B' * C) := by
      rw [sub_mul, mul_sub, hYB, hBY]
    rw [(Lemma18iii.conj_traces_trace_det_eq hdet hcomm).2]
    simp [hC, hB', Matrix.det_fin_two]
    ring

end CFSG.GH74.GLS.IVK.Proofs2
