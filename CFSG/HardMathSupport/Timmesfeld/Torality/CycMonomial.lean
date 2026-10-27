module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open Matrix MatrixGroups

variable {K : Type*} [Field K]

@[expose] def cycMat5 (a : Fin 5 → K) : Matrix (Fin 5) (Fin 5) K :=
  !![0, 0, 0, 0, a 4; a 0, 0, 0, 0, 0; 0, a 1, 0, 0, 0; 0, 0, a 2, 0, 0; 0, 0, 0, a 3, 0]

theorem cycMat5_mul_diagonal (a d : Fin 5 → K) :
    cycMat5 a * Matrix.diagonal d = cycMat5 (fun j => a j * d j) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat5, Matrix.mul_apply, Matrix.diagonal_apply]

@[expose] def cycEigen5 (ω : K) (a : Fin 5 → K) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.diagonal ![1, a 0, a 0 * a 1, a 0 * a 1 * a 2, a 0 * a 1 * a 2 * a 3] *
    Matrix.vandermonde fun k : Fin 5 => ω ^ (k : ℕ)

set_option linter.unusedSimpArgs false in
theorem cycMat5_mul_cycEigen5 {ω : K} (hω : ω ^ 5 = 1) {a : Fin 5 → K}
    (ha : a 0 * a 1 * a 2 * a 3 * a 4 = 1) :
    cycMat5 a * cycEigen5 ω a =
      cycEigen5 ω a * Matrix.diagonal fun k : Fin 5 => ω ^ (5 - (k : ℕ)) := by
  have h5 : ω ^ 5 = ω ^ 0 := by
    rw [show 5 = 5 * 1 + 0 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h6 : ω ^ 6 = ω ^ 1 := by
    rw [show 6 = 5 * 1 + 1 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h7 : ω ^ 7 = ω ^ 2 := by
    rw [show 7 = 5 * 1 + 2 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h8 : ω ^ 8 = ω ^ 3 := by
    rw [show 8 = 5 * 1 + 3 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h9 : ω ^ 9 = ω ^ 4 := by
    rw [show 9 = 5 * 1 + 4 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h10 : ω ^ 10 = ω ^ 0 := by
    rw [show 10 = 5 * 2 + 0 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h11 : ω ^ 11 = ω ^ 1 := by
    rw [show 11 = 5 * 2 + 1 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h12 : ω ^ 12 = ω ^ 2 := by
    rw [show 12 = 5 * 2 + 2 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h13 : ω ^ 13 = ω ^ 3 := by
    rw [show 13 = 5 * 2 + 3 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h14 : ω ^ 14 = ω ^ 4 := by
    rw [show 14 = 5 * 2 + 4 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h15 : ω ^ 15 = ω ^ 0 := by
    rw [show 15 = 5 * 3 + 0 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h16 : ω ^ 16 = ω ^ 1 := by
    rw [show 16 = 5 * 3 + 1 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h17 : ω ^ 17 = ω ^ 2 := by
    rw [show 17 = 5 * 3 + 2 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h18 : ω ^ 18 = ω ^ 3 := by
    rw [show 18 = 5 * 3 + 3 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h19 : ω ^ 19 = ω ^ 4 := by
    rw [show 19 = 5 * 3 + 4 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h20 : ω ^ 20 = ω ^ 0 := by
    rw [show 20 = 5 * 4 + 0 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h21 : ω ^ 21 = ω ^ 1 := by
    rw [show 21 = 5 * 4 + 1 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h22 : ω ^ 22 = ω ^ 2 := by
    rw [show 22 = 5 * 4 + 2 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h23 : ω ^ 23 = ω ^ 3 := by
    rw [show 23 = 5 * 4 + 3 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h24 : ω ^ 24 = ω ^ 4 := by
    rw [show 24 = 5 * 4 + 4 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have h25 : ω ^ 25 = ω ^ 0 := by
    rw [show 25 = 5 * 5 + 0 from by norm_num, pow_add, pow_mul, hω, one_pow, one_mul]
  have hprod : ∀ x : K, a 4 * a 0 * a 1 * a 2 * a 3 * x = x := fun x => by
    linear_combination x * ha
  ext i k
  simp only [cycMat5, cycEigen5, Matrix.mul_apply, Fin.sum_univ_five, Matrix.diagonal_apply,
    Matrix.vandermonde_apply]
  fin_cases i <;> fin_cases k <;>
    simp <;>
    ring_nf <;>
    (try simp only [h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]) <;>
    first | (linear_combination ha) | exact hprod _ | (linear_combination ω * ha) | ring1


theorem exists_sln_conj_of_eigen {n : ℕ} {M Q : Matrix (Fin n) (Fin n) K} {d : Fin n → K}
    (hQ : Q.det ≠ 0) (hd : ∏ i, d i = 1) (hMQ : M * Q = Q * Matrix.diagonal d)
    (m : SL(n, K)) (hm : (m : Matrix (Fin n) (Fin n) K) = M) :
    ∃ g : SL(n, K), ((g⁻¹ * m * g : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal d := by
  cases n with
  | zero => exact ⟨1, by ext i; exact i.elim0⟩
  | succ n =>
  set t : K := (Q.det)⁻¹ with ht
  set D : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.diagonal (Function.update 1 0 t) with hD
  have hdetD : D.det = t := by
    simp only [hD, Matrix.det_diagonal]
    rw [Finset.prod_eq_single 0]
    · simp
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · simp
  have hdet : (Q * D).det = 1 := by
    rw [Matrix.det_mul, hdetD, ht, mul_inv_cancel₀ hQ]
  have hΔdet : (Matrix.diagonal d).det = 1 := by
    simp [Matrix.det_diagonal, hd]
  let g : SL(n + 1, K) := ⟨Q * D, hdet⟩
  let Δ : SL(n + 1, K) := ⟨Matrix.diagonal d, hΔdet⟩
  have hcomm : Matrix.diagonal d * D = D * Matrix.diagonal d := by
    simp only [hD, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hg : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = Q * D := rfl
  have hΔ : (Δ : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = Matrix.diagonal d := rfl
  have hmg : m * g = g * Δ := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hm, hg, hΔ,
      ← Matrix.mul_assoc, hMQ, Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
  refine ⟨g, ?_⟩
  have : g⁻¹ * m * g = Δ := by
    rw [mul_assoc, hmg, inv_mul_cancel_left]
  rw [this]

theorem exists_sl5_conj_diagonal_cyc {ω : K} (hω : IsPrimitiveRoot ω 5) {a : Fin 5 → K}
    (ha : a 0 * a 1 * a 2 * a 3 * a 4 = 1) (m : SL(5, K))
    (hm : (m : Matrix (Fin 5) (Fin 5) K) = cycMat5 a) :
    ∃ g : SL(5, K), ∃ d : Fin 5 → K, ((g⁻¹ * m * g : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.diagonal d := by
  have hω5 : ω ^ 5 = 1 := hω.pow_eq_one
  have ha0 : a 0 ≠ 0 := fun h => by simp [h] at ha
  have ha1 : a 1 ≠ 0 := fun h => by simp [h] at ha
  have ha2 : a 2 ≠ 0 := fun h => by simp [h] at ha
  have ha3 : a 3 ≠ 0 := fun h => by simp [h] at ha
  have hVdet : (Matrix.vandermonde fun k : Fin 5 => ω ^ (k : ℕ)).det ≠ 0 := by
    refine Matrix.det_vandermonde_ne_zero_iff.2 fun i j hij => ?_
    exact Fin.ext (hω.pow_inj i.2 j.2 hij)
  have hQ : (cycEigen5 ω a).det ≠ 0 := by
    rw [cycEigen5, Matrix.det_mul, Matrix.det_diagonal]
    refine mul_ne_zero ?_ hVdet
    simp [Fin.prod_univ_five, ha0, ha1, ha2, ha3]
  have hΔ : ∏ k : Fin 5, ω ^ (5 - (k : ℕ)) = 1 := by
    simp only [Fin.prod_univ_five]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    have h4 : ((3 : Fin 5) : ℕ) = 3 := rfl
    have h5 : ((4 : Fin 5) : ℕ) = 4 := rfl
    rw [h4, h5]
    have : ω ^ (5 - 0) * ω ^ (5 - 1) * ω ^ (5 - 2) * ω ^ (5 - 3) * ω ^ (5 - 4) = (ω ^ 5) ^ 3 := by
      norm_num
      ring
    rw [this, hω5, one_pow]
  exact ⟨(exists_sln_conj_of_eigen hQ hΔ (cycMat5_mul_cycEigen5 hω5 ha) m hm).choose,
    _, (exists_sln_conj_of_eigen hQ hΔ (cycMat5_mul_cycEigen5 hω5 ha) m hm).choose_spec⟩

end CFSG.HardMathSupport.Timmesfeld.Torality
