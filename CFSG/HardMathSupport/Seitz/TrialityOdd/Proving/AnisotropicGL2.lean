module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open Matrix

variable {K : Type*} [Field K]

theorem eval_charpoly_fin_two (M : Matrix (Fin 2) (Fin 2) K) (a : K) :
    (M.charpoly).eval a = a * a - M.trace * a + M.det := by
  simp [Matrix.charpoly, Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

theorem sub_smul_one_mul_sub_smul_one (M : Matrix (Fin 2) (Fin 2) K) (x y : K) :
    (M - x • (1 : Matrix (Fin 2) (Fin 2) K)) * (M - y • 1) =
      M * M - (x + y) • M + (x * y) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul,
    add_smul, smul_sub]
  rw [mul_comm y x]
  abel

theorem mul_self_sub_trace_smul_add_det (M : Matrix (Fin 2) (Fin 2) K) :
    M * M - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;>
    ring

theorem pow_mul_sub_smul_one {M : Matrix (Fin 2) (Fin 2) K} {a d : K}
    (hfac : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)) * (M - d • 1) = 0) (k : ℕ) :
    M ^ k * (M - d • (1 : Matrix (Fin 2) (Fin 2) K)) = a ^ k • (M - d • 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : M * (M - d • (1 : Matrix (Fin 2) (Fin 2) K)) = a • (M - d • 1) := by
      have e : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)) * (M - d • 1) =
          M * (M - d • 1) - a • (M - d • 1) := by
        rw [sub_mul, smul_mul_assoc, one_mul]
      rw [hfac] at e
      exact sub_eq_zero.mp e.symm
    rw [pow_succ', mul_assoc, ih, Matrix.mul_smul, h1, smul_smul, pow_succ]

theorem scalar_of_double_root {M : Matrix (Fin 2) (Fin 2) K} {a c : K} {r : ℕ}
    (hr : 0 < r) (hrK : (r : K) ≠ 0) (ha0 : a ≠ 0)
    (hfac : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)) * (M - a • 1) = 0)
    (hc : M ^ r = c • 1) :
    ∃ c' : K, M = c' • (1 : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨N, hN⟩ : ∃ N, N = M - a • (1 : Matrix (Fin 2) (Fin 2) K) := ⟨_, rfl⟩
  have hN2 : N * N = 0 := by rw [hN]; exact hfac
  have hMN : M = a • (1 : Matrix (Fin 2) (Fin 2) K) + N := by rw [hN]; abel
  have hform : ∀ k : ℕ, M ^ (k + 1) =
      a ^ (k + 1) • (1 : Matrix (Fin 2) (Fin 2) K) + (((k + 1 : ℕ) : K) * a ^ k) • N := by
    intro k
    induction k with
    | zero => simp [hMN]
    | succ k ih =>
      rw [pow_succ, ih, hMN]
      have hsq : N * N = 0 := hN2
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        hsq, smul_zero, add_zero]
      rw [← sub_eq_zero]
      module
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have hr' := hform k
  rw [hc] at hr'
  have hβ : ((k + 1 : ℕ) : K) * a ^ k ≠ 0 := mul_ne_zero hrK (pow_ne_zero _ ha0)
  have hsub : (((k + 1 : ℕ) : K) * a ^ k) • N = (c - a ^ (k + 1)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [sub_smul, hr']
    abel
  refine ⟨a + (((k + 1 : ℕ) : K) * a ^ k)⁻¹ * (c - a ^ (k + 1)), ?_⟩
  rw [hMN, ← inv_smul_smul₀ hβ N, hsub, smul_smul, add_smul]

theorem charpoly_eval_ne_zero_of_pow_scalar {K : Type*} [Field K] [Finite K]
    {E : GL (Fin 2) K} {r : ℕ} (hr : r.Prime) (_hr2 : r ≠ 2) (hrK : (r : K) ≠ 0)
    (hr1 : ¬ r ∣ Nat.card K - 1)
    (hpow : ∃ c : K, (E : Matrix (Fin 2) (Fin 2) K) ^ r = c • 1)
    (hns : ¬ ∃ c : K, (E : Matrix (Fin 2) (Fin 2) K) = c • 1) (a : K) :
    ((E : Matrix (Fin 2) (Fin 2) K).charpoly).eval a ≠ 0 := by
  classical
  have := Fact.mk hr
  obtain ⟨c, hc⟩ := hpow
  set M : Matrix (Fin 2) (Fin 2) K := (E : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hns' : ∀ c' : K, M ≠ c' • 1 := fun c' h => hns ⟨c', h⟩
  have hdet : M.det ≠ 0 := by
    have hu := E.isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    exact hu.ne_zero
  intro hroot
  rw [eval_charpoly_fin_two] at hroot
  obtain ⟨d, hd⟩ : ∃ d, a + d = M.trace := ⟨M.trace - a, by ring⟩
  rw [← hd] at hroot
  have had : a * d = M.det := by linear_combination (-1 : K) * hroot
  have hfac : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)) * (M - d • 1) = 0 := by
    rw [sub_smul_one_mul_sub_smul_one, hd, had]
    exact mul_self_sub_trace_smul_add_det M
  have hfac' : (M - d • (1 : Matrix (Fin 2) (Fin 2) K)) * (M - a • 1) = 0 := by
    rw [sub_smul_one_mul_sub_smul_one, add_comm d a, hd, mul_comm d a, had]
    exact mul_self_sub_trace_smul_add_det M
  have hd0 : d ≠ 0 := by
    intro h; apply hdet; rw [← had, h, mul_zero]
  have ha0 : a ≠ 0 := by
    intro h; apply hdet; rw [← had, h, zero_mul]
  have hMd : M - d • (1 : Matrix (Fin 2) (Fin 2) K) ≠ 0 :=
    fun h => hns' d (sub_eq_zero.mp h)
  have hMa : M - a • (1 : Matrix (Fin 2) (Fin 2) K) ≠ 0 :=
    fun h => hns' a (sub_eq_zero.mp h)
  have hrd : a ^ r = d ^ r := by
    have h1 := pow_mul_sub_smul_one hfac r
    rw [hc, smul_mul_assoc, one_mul] at h1
    have h2 := pow_mul_sub_smul_one hfac' r
    rw [hc, smul_mul_assoc, one_mul] at h2
    have e1 : c = a ^ r := smul_left_injective K hMd h1
    have e2 : c = d ^ r := smul_left_injective K hMa h2
    exact e1.symm.trans e2
  by_cases hda : a = d
  · subst hda
    obtain ⟨c', hc'⟩ := scalar_of_double_root (M := M) (a := a) (c := c) (r := r)
      hr.pos hrK ha0 hfac hc
    exact hns ⟨c', hc'⟩
  · have hx0 : a * d⁻¹ ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hd0)
    have hx1 : (a * d⁻¹) ^ r = 1 := by
      rw [mul_pow, inv_pow, hrd, mul_inv_cancel₀ (pow_ne_zero _ hd0)]
    have hx2 : a * d⁻¹ ≠ 1 := by
      intro h
      exact hda ((mul_inv_eq_one₀ hd0).mp h)
    have hord : orderOf (a * d⁻¹) = r := orderOf_eq_prime hx1 hx2
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card] at hr1
    apply hr1
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one _ hx0)

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
