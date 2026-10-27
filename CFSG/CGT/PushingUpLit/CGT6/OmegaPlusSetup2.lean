module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open Matrix

variable {F : Type*} [Field F]

theorem eq_zero_of_forall_sl_mul (M : Matrix (Fin 2) (Fin 2) F)
    (h : ∀ s : SpecialLinearGroup (Fin 2) F, (s : Matrix (Fin 2) (Fin 2) F) * M = M) : M = 0 := by
  have h1 := h ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have h2 := h ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  ext i j
  have e1 := congrFun (congrFun h1 0) j
  have e2 := congrFun (congrFun h2 1) j
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2
  fin_cases i
  · simpa using e2
  · simpa using e1

theorem eq_smul_one_of_forall_sl_comm (γ : Matrix (Fin 2) (Fin 2) F)
    (h : ∀ s : SpecialLinearGroup (Fin 2) F,
      (s : Matrix (Fin 2) (Fin 2) F) * γ = γ * (s : Matrix (Fin 2) (Fin 2) F)) :
    γ = γ 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h1 := h ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have h2 := h ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h1 0) 1
  have e3 := congrFun (congrFun h2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa using e3
  · simpa using e1
  · simp
    linear_combination e2

theorem sub_one_sq_eq_zero_of_sq_eq_one [CharP F 2] {K : Matrix (Fin 2) (Fin 2) F}
    (hK : K * K = 1) : (K - 1) * (K - 1) = 0 := by
  rw [sub_mul, mul_sub, mul_sub, hK, mul_one, one_mul, one_mul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.zero_apply]
  linear_combination ((1 : Matrix (Fin 2) (Fin 2) F) i j - K i j) *
    (CharTwo.two_eq_zero : (2 : F) = 0)

theorem cross_eq_zero_of_vecMul {N : Matrix (Fin 2) (Fin 2) F} (hN0 : N ≠ 0) {r ρ : Fin 2 → F}
    (hr : r ᵥ* N = 0) (hρ : ρ ᵥ* N = 0) : r 0 * ρ 1 - r 1 * ρ 0 = 0 := by
  let S : Matrix (Fin 2) (Fin 2) F := Matrix.of ![r, ρ]
  have hS : S * N = 0 := by
    ext a b
    fin_cases a
    · simpa [S, Matrix.mul_apply, Matrix.vecMul, dotProduct] using congrFun hr b
    · simpa [S, Matrix.mul_apply, Matrix.vecMul, dotProduct] using congrFun hρ b
  have h1 : S.det • N = 0 := by
    calc S.det • N = (S.det • (1 : Matrix (Fin 2) (Fin 2) F)) * N := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = S.adjugate * S * N := by rw [Matrix.adjugate_mul]
      _ = 0 := by rw [Matrix.mul_assoc, hS, Matrix.mul_zero]
  have h2 : S.det = 0 := (smul_eq_zero.mp h1).resolve_right hN0
  rw [Matrix.det_fin_two] at h2
  simpa [S] using h2

theorem eq_smul_of_cross {r ρ τ : Fin 2 → F} (hτ : ρ ⬝ᵥ τ = 1)
    (h : r 0 * ρ 1 - r 1 * ρ 0 = 0) : r = (r ⬝ᵥ τ) • ρ := by
  simp only [dotProduct, Fin.sum_univ_two] at hτ ⊢
  ext k
  fin_cases k
  · simp
    linear_combination (-r 0) * hτ + τ 1 * h
  · simp
    linear_combination (-r 1) * hτ - τ 0 * h

theorem exists_row_of_sq_eq_zero {N : Matrix (Fin 2) (Fin 2) F} (hN : N * N = 0) (hN0 : N ≠ 0) :
    ∃ σ τ : Fin 2 → F, (σ ᵥ* N) ⬝ᵥ τ = 1 ∧
      ∀ r : Fin 2 → F, r ᵥ* N = 0 → r = (r ⬝ᵥ τ) • (σ ᵥ* N) := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hN0 (Matrix.ext fun i j => h i j)
  have hρ : Pi.single i 1 ᵥ* N = fun k => N i k := by
    rw [Matrix.single_vecMul, one_smul]
    rfl
  have hτ : (Pi.single i 1 ᵥ* N) ⬝ᵥ Pi.single j (N i j)⁻¹ = 1 := by
    rw [hρ, dotProduct_single, mul_inv_cancel₀ hij]
  refine ⟨Pi.single i 1, Pi.single j (N i j)⁻¹, hτ, fun r hr => eq_smul_of_cross hτ ?_⟩
  refine cross_eq_zero_of_vecMul hN0 hr ?_
  rw [Matrix.vecMul_vecMul, hN, Matrix.vecMul_zero]

theorem vecMul_eq_of_comm_sq_eq_zero [CharP F 2] {N L : Matrix (Fin 2) (Fin 2) F}
    (hN : N * N = 0) (hN0 : N ≠ 0) (hL : L.det = 1) (hLN : L * N = N * L) {r : Fin 2 → F}
    (hr : r ᵥ* N = 0) : r ᵥ* L = r := by
  obtain ⟨σ, τ, hτ, hker⟩ := exists_row_of_sq_eq_zero hN hN0
  obtain ⟨ρ, hρ⟩ : ∃ ρ, σ ᵥ* N = ρ := ⟨_, rfl⟩
  rw [hρ] at hτ hker
  have hρN : ρ ᵥ* N = 0 := by rw [← hρ, Matrix.vecMul_vecMul, hN, Matrix.vecMul_zero]
  have h1 : ρ ᵥ* L = (σ ᵥ* L) ᵥ* N := by
    rw [← hρ, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hLN]
  have h2 : ((σ ᵥ* L) ᵥ* N) ᵥ* N = 0 := by
    rw [Matrix.vecMul_vecMul, hN, Matrix.vecMul_zero]
  obtain ⟨l, hl⟩ : ∃ l, ((σ ᵥ* L) ᵥ* N) ⬝ᵥ τ = l := ⟨_, rfl⟩
  have h3 : ρ ᵥ* L = l • ρ := by rw [h1, ← hl]; exact hker _ h2
  have h4 : (σ ᵥ* L - l • σ) ᵥ* N = 0 := by
    rw [Matrix.sub_vecMul, smul_vecMul, ← h1, h3, hρ, sub_self]
  obtain ⟨κ, hκ⟩ : ∃ κ, (σ ᵥ* L - l • σ) ⬝ᵥ τ = κ := ⟨_, rfl⟩
  have h5 : σ ᵥ* L = l • σ + κ • ρ := by
    have := hker _ h4
    rw [hκ] at this
    rw [← this]
    abel
  let S : Matrix (Fin 2) (Fin 2) F := Matrix.of ![σ, ρ]
  have hS : S.det ≠ 0 := by
    intro h0
    rw [Matrix.det_fin_two] at h0
    have hσ : σ = (σ ⬝ᵥ τ) • ρ := eq_smul_of_cross hτ (by simpa [S] using h0)
    have hρ0 : ρ = 0 := by
      rw [← hρ, hσ, smul_vecMul, hρN, smul_zero]
    rw [hρ0, zero_dotProduct] at hτ
    exact zero_ne_one hτ
  have hST : S * L = !![l, κ; 0, l] * S := by
    ext a b
    fin_cases a
    · have := congrFun h5 b
      simp [S, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this ⊢
      linear_combination this
    · have := congrFun h3 b
      simp [S, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this ⊢
      linear_combination this
  have hl2 : l ^ 2 = 1 := by
    have h6 := congrArg Matrix.det hST
    rw [Matrix.det_mul, Matrix.det_mul, hL, Matrix.det_fin_two_of] at h6
    have h7 : (l ^ 2 - 1) * S.det = 0 := by linear_combination (-1 : F) * h6
    exact sub_eq_zero.mp ((mul_eq_zero.mp h7).resolve_right hS)
  have hl1 : l = 1 := by
    have h8 : (l - 1) ^ 2 = 0 := by
      linear_combination hl2 + (1 - l) * (CharTwo.two_eq_zero : (2 : F) = 0)
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h8)
  rw [hker r hr, smul_vecMul, h3, hl1, one_smul]

theorem mul_row_eq_vecMul (M N : Matrix (Fin 2) (Fin 2) F) (i : Fin 2) :
    (M * N) i = (fun k => M i k) ᵥ* N := by
  ext k
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem exists_vecMulVec_of_sq_eq_zero {N : Matrix (Fin 2) (Fin 2) F} (hN : N * N = 0)
    (hN0 : N ≠ 0) :
    ∃ σ τ : Fin 2 → F, (σ ᵥ* N) ⬝ᵥ τ = 1 ∧
      ∀ M : Matrix (Fin 2) (Fin 2) F, M * N = 0 → M = vecMulVec (M *ᵥ τ) (σ ᵥ* N) := by
  obtain ⟨σ, τ, hτ, hker⟩ := exists_row_of_sq_eq_zero hN hN0
  refine ⟨σ, τ, hτ, fun M hM => ?_⟩
  ext i j
  have hr : (fun k => M i k) ᵥ* N = 0 := by rw [← mul_row_eq_vecMul, hM]; rfl
  have := congrFun (hker _ hr) j
  simpa [vecMulVec_apply, Matrix.mulVec, dotProduct] using this

theorem exists_mul_eq_of_mul_eq_zero {N M : Matrix (Fin 2) (Fin 2) F} (hN : N * N = 0)
    (hN0 : N ≠ 0) (hM : M * N = 0) : ∃ X, M = X * N := by
  obtain ⟨σ, τ, -, hker⟩ := exists_vecMulVec_of_sq_eq_zero hN hN0
  exact ⟨vecMulVec (M *ᵥ τ) σ, by rw [Matrix.vecMulVec_mul, ← hker M hM]⟩

theorem mul_eq_of_comm_sq_eq_zero [CharP F 2] {N L M : Matrix (Fin 2) (Fin 2) F}
    (hN : N * N = 0) (hN0 : N ≠ 0) (hL : L.det = 1) (hLN : L * N = N * L) (hM : M * N = 0) :
    M * L = M := by
  ext i j
  have hr : (fun k => M i k) ᵥ* N = 0 := by rw [← mul_row_eq_vecMul, hM]; rfl
  have := congrFun (vecMul_eq_of_comm_sq_eq_zero hN hN0 hL hLN hr) j
  rw [mul_row_eq_vecMul]
  exact this

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
