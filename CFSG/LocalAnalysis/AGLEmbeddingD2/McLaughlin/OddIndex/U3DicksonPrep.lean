module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.GL2NonsplitTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2Torus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.BenderSuzuki.MatrixGroups
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2

section SL2

variable {K : Type} [Field K]

@[expose] def dSLu (w : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(w : K), 0; 0, ((w⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

@[expose] def swSL : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_dSLu (w : Kˣ) :
    ((dSLu w : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(w : K), 0; 0, ((w⁻¹ : Kˣ) : K)] := rfl

theorem coe_swSL :
    ((swSL : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

theorem dSLu_mul (w v : Kˣ) : dSLu w * dSLu v = (dSLu (w * v) : SpecialLinearGroup (Fin 2) K) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_dSLu, coe_dSLu, coe_dSLu, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem dSLu_one : (dSLu (1 : Kˣ) : SpecialLinearGroup (Fin 2) K) = 1 := by
  ext i j
  rw [coe_dSLu]
  fin_cases i <;> fin_cases j <;> simp

theorem dSLu_pow (w : Kˣ) (n : ℕ) : (dSLu w : SpecialLinearGroup (Fin 2) K) ^ n = dSLu (w ^ n) := by
  induction n with
  | zero => simp [dSLu_one]
  | succ n ih => rw [pow_succ, ih, dSLu_mul, ← pow_succ]

theorem swSL_mul_dSLu (w : Kˣ) :
    (swSL : SpecialLinearGroup (Fin 2) K) * dSLu w = dSLu w⁻¹ * swSL := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_dSLu, coe_dSLu,
    coe_swSL, Matrix.mul_fin_two, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

theorem dSLu_inv (w : Kˣ) : (dSLu w : SpecialLinearGroup (Fin 2) K)⁻¹ = dSLu w⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, dSLu_mul, mul_inv_cancel, dSLu_one]

theorem dSLu_not_mem_center {w : Kˣ} (h3 : w ^ 3 = 1) (h1 : w ≠ 1) :
    (dSLu w : SpecialLinearGroup (Fin 2) K) ∉ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
  intro hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h00 := congrFun (congrFun hrz 0) 0
  have h11 := congrFun (congrFun hrz 1) 1
  simp [dSLu, Matrix.scalar_apply] at h00 h11
  have hw : (w : K) = (w : K)⁻¹ := h00.symm.trans h11
  have hw' : w = w⁻¹ := Units.ext (by rw [Units.val_inv_eq_inv_val]; exact hw)
  apply h1
  have h2 : w * w = 1 := by
    calc w * w = w * w⁻¹ := by rw [← hw']
      _ = 1 := mul_inv_cancel w
  calc w = w ^ 3 := by rw [show w ^ 3 = (w * w) * w by rw [_root_.pow_succ, _root_.pow_two], h2, one_mul]
    _ = 1 := h3

end SL2

section PSL

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem projPSL_dSLu_pow_three {w : Kˣ} (h3 : w ^ 3 = 1) :
    (projPSL K (dSLu w)) ^ 3 = 1 := by
  rw [← map_pow, dSLu_pow, h3, dSLu_one, map_one]

omit [Finite K] in
theorem orderOf_projPSL_dSLu {w : Kˣ} (h3 : w ^ 3 = 1) (h1 : w ≠ 1) :
    orderOf (projPSL K (dSLu w)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (projPSL_dSLu_pow_three h3) ?_
  intro h
  exact dSLu_not_mem_center h3 h1 (projPSL_eq_one_iff.mp h)

omit [Finite K] in
theorem projPSL_swSL_conj (w : Kˣ) :
    projPSL K swSL * projPSL K (dSLu w) * (projPSL K swSL)⁻¹ = (projPSL K (dSLu w))⁻¹ := by
  have h : (swSL : SpecialLinearGroup (Fin 2) K) * dSLu w * swSL⁻¹ = (dSLu w)⁻¹ := by
    rw [dSLu_inv]
    exact mul_inv_eq_iff_eq_mul.mpr (swSL_mul_dSLu w)
  have := congrArg (projPSL K) h
  simpa [map_mul, map_inv] using this

theorem exists_cube_root_unity (hq3 : Nat.card K % 3 = 1) :
    ∃ w : Kˣ, w ^ 3 = 1 ∧ w ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    have : 1 ≤ Nat.card K := Nat.card_pos
    omega
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hdvd
  refine ⟨w, ?_, ?_⟩
  · rw [← hw]
    exact pow_orderOf_eq_one w
  · intro h1
    rw [h1, orderOf_one] at hw
    omega

end PSL

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
