module

public import CFSG.LieType.Steinberg.PartB

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo

open Matrix CFSG.LieType.Steinberg

variable {K : Type*} [Field K]

theorem conj_sl2Upper_coe (m : SpecialLinearGroup (Fin 2) K) (t : K) :
    ((m * sl2Upper t * m⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1 - m 0 0 * m 1 0 * t, m 0 0 ^ 2 * t; -(m 1 0 ^ 2 * t), 1 + m 0 0 * m 1 0 * t] := by
  have hdet : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
    have h := m.2
    rwa [Matrix.det_fin_two] at h
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination -hdet | linear_combination hdet | ring

theorem eq_refl_of_conj_sl2Upper (σ : K ≃+* K) (m : SpecialLinearGroup (Fin 2) K) (lam : K)
    (h : ∀ s : K, m * sl2Upper (σ s) * m⁻¹ = sl2Upper (lam * s)) : σ = RingEquiv.refl K := by
  have hentry : ∀ (s : K) (i j : Fin 2),
      (!![1 - m 0 0 * m 1 0 * σ s, m 0 0 ^ 2 * σ s; -(m 1 0 ^ 2 * σ s),
        1 + m 0 0 * m 1 0 * σ s] : Matrix (Fin 2) (Fin 2) K) i j =
        (!![1, lam * s; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j := by
    intro s i j
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) i j) (h s)
    simp only [conj_sl2Upper_coe] at h1
    exact h1
  have hc : m 1 0 = 0 := by
    have h10 := hentry 1 1 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, map_one, mul_one,
      neg_eq_zero] at h10
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h10
  have h01 : ∀ s : K, m 0 0 ^ 2 * σ s = lam * s := by
    intro s
    have h1 := hentry s 0 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one] at h1
    exact h1
  have hdet : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
    have h := m.2
    rwa [Matrix.det_fin_two] at h
  have ha : m 0 0 ≠ 0 := by
    intro ha
    rw [ha, hc] at hdet
    simp at hdet
  have hlam : lam = m 0 0 ^ 2 := by
    have := h01 1
    rw [map_one, mul_one, mul_one] at this
    exact this.symm
  ext s
  have h2 := h01 s
  rw [hlam] at h2
  exact mul_left_cancel₀ (pow_ne_zero 2 ha) h2

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo
