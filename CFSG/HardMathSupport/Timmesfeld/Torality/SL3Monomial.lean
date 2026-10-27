module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open Matrix MatrixGroups

variable {K : Type*} [Field K]

@[expose] def monoM₁ (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![0, 0, c; a, 0, 0; 0, b, 0]

@[expose] def monoM₂ (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![0, a, 0; 0, 0, b; c, 0, 0]

@[expose] def fourier3 (ω : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 1; 1, ω ^ 2, ω; 1, ω, ω ^ 2]

theorem det_fourier3 {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (fourier3 ω).det = 3 * (ω - ω ^ 2) := by
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  simp [fourier3, Matrix.det_fin_three]
  linear_combination ω * h3

theorem exists_sl3_conj_of_eigen {M Q : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K}
    (hQ : Q.det ≠ 0) (hd : d 0 * d 1 * d 2 = 1) (hMQ : M * Q = Q * Matrix.diagonal d)
    (m : SL(3, K)) (hm : (m : Matrix (Fin 3) (Fin 3) K) = M) :
    ∃ g : SL(3, K), ((g⁻¹ * m * g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d := by
  set t : K := (Q.det)⁻¹ with ht
  set D : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![t, 1, 1] with hD
  have hdetD : D.det = t := by
    simp [hD, Matrix.det_diagonal, Fin.prod_univ_three]
  have hdet : (Q * D).det = 1 := by
    rw [Matrix.det_mul, hdetD, ht, mul_inv_cancel₀ hQ]
  have hΔdet : (Matrix.diagonal d).det = 1 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, hd]
  let g : SL(3, K) := ⟨Q * D, hdet⟩
  let Δ : SL(3, K) := ⟨Matrix.diagonal d, hΔdet⟩
  have hcomm : Matrix.diagonal d * D = D * Matrix.diagonal d := by
    simp only [hD, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hg : (g : Matrix (Fin 3) (Fin 3) K) = Q * D := rfl
  have hΔ : (Δ : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d := rfl
  have hmg : m * g = g * Δ := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hm, hg, hΔ,
      ← Matrix.mul_assoc, hMQ, Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
  refine ⟨g, ?_⟩
  have : g⁻¹ * m * g = Δ := by
    rw [mul_assoc, hmg, inv_mul_cancel_left]
  rw [this]

theorem exists_sl3_conj_M₁ {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0) {a b c : K}
    (habc : a * b * c = 1) (m : SL(3, K)) (hm : (m : Matrix (Fin 3) (Fin 3) K) = monoM₁ a b c) :
    ∃ g : SL(3, K), ((g⁻¹ * m * g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, ω, ω ^ 2] := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have ha : a ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one habc)
  have hb : b ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul_eq_one habc)
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω3
  have hω1 : ω ≠ 1 := fun h => h3 (by rw [h] at hω; linear_combination hω)
  let Q : Matrix (Fin 3) (Fin 3) K := !![1, 1, 1; a, a * ω ^ 2, a * ω; a * b, a * b * ω, a * b * ω ^ 2]
  have hdetQ : Q.det = a ^ 2 * b * (3 * (ω - ω ^ 2)) := by
    simp [Q, Matrix.det_fin_three]
    linear_combination (a ^ 2 * b * ω) * hω3
  have hQ : Q.det ≠ 0 := by
    rw [hdetQ]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) hb) (mul_ne_zero h3 ?_)
    intro h
    have : ω * (1 - ω) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hω0 h'
    · exact hω1 (by linear_combination -h')
  refine exists_sl3_conj_of_eigen hQ (by simp; linear_combination hω3) ?_ m hm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q, monoM₁, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.diagonal_apply]
  all_goals first
    | ring1
    | linear_combination habc
    | linear_combination ω * habc
    | linear_combination ω ^ 2 * habc
    | linear_combination (-a) * hω3
    | linear_combination (-(a * b * ω)) * hω3

theorem exists_sl3_conj_M₂ {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0) {a b c : K}
    (habc : a * b * c = 1) (m : SL(3, K)) (hm : (m : Matrix (Fin 3) (Fin 3) K) = monoM₂ a b c) :
    ∃ g : SL(3, K), ((g⁻¹ * m * g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, ω, ω ^ 2] := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have ha : a ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one habc)
  have hb : b ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul_eq_one habc)
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω3
  have hω1 : ω ≠ 1 := fun h => h3 (by rw [h] at hω; linear_combination hω)
  let Q : Matrix (Fin 3) (Fin 3) K := !![a * b, a * b, a * b; b, ω * b, ω ^ 2 * b; 1, ω ^ 2, ω]
  have hdetQ : Q.det = a * b ^ 2 * (3 * (ω ^ 2 - ω)) := by
    simp [Q, Matrix.det_fin_three]
    linear_combination (-(a * b ^ 2 * ω)) * hω3
  have hQ : Q.det ≠ 0 := by
    rw [hdetQ]
    refine mul_ne_zero (mul_ne_zero ha (pow_ne_zero 2 hb)) (mul_ne_zero h3 ?_)
    intro h
    have : ω * (ω - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hω0 h'
    · exact hω1 (by linear_combination h')
  refine exists_sl3_conj_of_eigen hQ (by simp; linear_combination hω3) ?_ m hm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q, monoM₂, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.diagonal_apply]
  all_goals first
    | ring1
    | linear_combination habc
    | linear_combination habc - hω3
    | linear_combination (-(b * ω)) * hω3

end CFSG.HardMathSupport.Timmesfeld.Torality
