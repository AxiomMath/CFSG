module

import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix
open scoped Fin.NatCast

variable {K : Type*} [Field K]

@[expose] def hX (ω : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal fun i => ω ^ (i : ℕ)

@[expose] def hP : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => if i = j + 1 then 1 else 0

theorem mul_hP_apply (A : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (A * (hP : Matrix (Fin 3) (Fin 3) K)) i j = A i (j + 1) := by
  simp [hP, Matrix.mul_apply]

theorem hP_mul_apply (A : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    ((hP : Matrix (Fin 3) (Fin 3) K) * A) i j = A (i - 1) j := by
  simp only [hP, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (i - 1)]
  · simp
  · intro k _ hk
    have : ¬ (i = k + 1) := fun h => hk (eq_sub_of_add_eq h.symm)
    simp [this]
  · simp

theorem hP_pow (n : ℕ) :
    (hP : Matrix (Fin 3) (Fin 3) K) ^ n =
      Matrix.of fun i j => if i = j + (n : Fin 3) then 1 else 0 := by
  induction n with
  | zero =>
    ext i j
    simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    simp only [hP, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (j + 1)]
    · have h : j + 1 + (n : Fin 3) = j + ((n + 1 : ℕ) : Fin 3) := by
        rw [Nat.cast_succ, add_assoc, add_comm 1 (n : Fin 3)]
      simp [h]
    · intro k _ hk
      simp [hk]
    · simp

theorem hP_pow_mul_hX_pow (ω : K) (a b : ℕ) (i j : Fin 3) :
    ((hP : Matrix (Fin 3) (Fin 3) K) ^ a * hX ω ^ b) i j =
      (if i = j + (a : Fin 3) then 1 else 0) * (ω ^ (j : ℕ)) ^ b := by
  rw [hX, Matrix.diagonal_pow, Matrix.mul_diagonal, hP_pow]
  rfl

theorem eq_pow_of_pow_three_eq_one {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {η : K}
    (hη : η ^ 3 = 1) : ∃ b : ℕ, b < 3 ∧ η = ω ^ b := by
  have hsum : ω ^ 2 + ω + 1 = 0 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hω1)
  have h : (η - 1) * ((η - ω) * (η - ω ^ 2)) = 0 := by
    linear_combination hη + (η - η ^ 2) * hsum + (η - 1) * hω3
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨0, by norm_num, by rw [pow_zero]; exact sub_eq_zero.1 h⟩
  · rcases mul_eq_zero.1 h with h | h
    · exact ⟨1, by norm_num, by rw [pow_one]; exact sub_eq_zero.1 h⟩
    · exact ⟨2, by norm_num, sub_eq_zero.1 h⟩

theorem pow_inj_fin_three {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {i j : Fin 3}
    (h : ω ^ (i : ℕ) = ω ^ (j : ℕ)) : i = j := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    calc ω = ω * ω ^ 2 := by rw [h2, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  have hω12 : ω ≠ ω ^ 2 := by
    intro h2
    apply hω1
    have : ω * (1 - ω) = 0 := by linear_combination h2
    have := (mul_eq_zero.1 this).resolve_left hω0
    linear_combination -this
  rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl <;>
    rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) j with rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso
       simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at h
       first
       | exact hω1 h.symm
       | exact hω2 h.symm
       | exact hω12 h
       | exact hω1 h
       | exact hω2 h
       | exact hω12 h.symm)

theorem matrix_eq_smul_pow_mul_pow {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (A : Matrix (Fin 3) (Fin 3) K) (hdet : A.det ≠ 0) (ζ η : K)
    (h1 : A * hX ω = ζ • (hX ω * A)) (h2 : A * (hP : Matrix (Fin 3) (Fin 3) K) = η • (hP * A)) :
    ∃ (c : K) (a b : ℕ), c ≠ 0 ∧
      A = c • ((hP : Matrix (Fin 3) (Fin 3) K) ^ a * hX ω ^ b) := by
  have e1 : ∀ i, A i 0 = ζ * (ω ^ (i : ℕ) * A i 0) := by
    intro i
    have := congrFun (congrFun h1 i) 0
    simpa [hX, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have e2 : ∀ i j, A i (j + 1) = η * A (i - 1) j := by
    intro i j
    have := congrFun (congrFun h2 i) j
    simpa [mul_hP_apply, hP_mul_apply] using this
  have f1 : ∀ i, A i 1 = η * A (i - 1) 0 := fun i => by simpa using e2 i 0
  have f2 : ∀ i, A i 2 = η * A (i - 1) 1 := fun i => by
    have := e2 i 1
    rwa [show (1 : Fin 3) + 1 = 2 from rfl] at this
  have f0 : ∀ i, A i 0 = η * A (i - 1) 2 := fun i => by
    have := e2 i 2
    rwa [show (2 : Fin 3) + 1 = 0 from rfl] at this
  obtain ⟨i₀, hi₀⟩ : ∃ i, A i 0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero 0 hcon)
  have huniq : ∀ i, A i 0 ≠ 0 → i = i₀ := by
    intro i hi
    have a1 : 1 = ζ * ω ^ (i : ℕ) := by
      apply mul_right_cancel₀ hi
      calc 1 * A i 0 = A i 0 := one_mul _
        _ = ζ * (ω ^ (i : ℕ) * A i 0) := e1 i
        _ = ζ * ω ^ (i : ℕ) * A i 0 := by ring
    have a2 : 1 = ζ * ω ^ (i₀ : ℕ) := by
      apply mul_right_cancel₀ hi₀
      calc 1 * A i₀ 0 = A i₀ 0 := one_mul _
        _ = ζ * (ω ^ (i₀ : ℕ) * A i₀ 0) := e1 i₀
        _ = ζ * ω ^ (i₀ : ℕ) * A i₀ 0 := by ring
    have hζ : ζ ≠ 0 := by
      rintro rfl
      simp at a1
    exact pow_inj_fin_three hω3 hω1 (mul_left_cancel₀ hζ (a1.symm.trans a2))
  have hcol0 : ∀ i, A i 0 = if i = i₀ then A i₀ 0 else 0 := by
    intro i
    by_cases hi : i = i₀
    · simp [hi]
    · have h0 : A i 0 = 0 := by
        by_contra hne
        exact hi (huniq i hne)
      simp [hi, h0]
  set v₀ := A i₀ 0 with hv₀
  have hcol1 : ∀ i, A i 1 = η * if i - 1 = i₀ then v₀ else 0 := by
    intro i
    rw [f1 i, hcol0 (i - 1)]
  have hcol2 : ∀ i, A i 2 = η * (η * if i - 1 - 1 = i₀ then v₀ else 0) := by
    intro i
    rw [f2 i, hcol1 (i - 1)]
  have hη3 : η ^ 3 = 1 := by
    have h0 := f0 i₀
    rw [hcol2 (i₀ - 1)] at h0
    have : i₀ - 1 - 1 - 1 = i₀ := by fin_cases i₀ <;> rfl
    rw [this] at h0
    simp only [↓reduceIte] at h0
    have : v₀ * (η ^ 3 - 1) = 0 := by linear_combination -h0
    have := (mul_eq_zero.1 this).resolve_left hi₀
    linear_combination this
  obtain ⟨b, -, hb⟩ := eq_pow_of_pow_three_eq_one hω3 hω1 hη3
  refine ⟨v₀, i₀.val, b, hi₀, ?_⟩
  ext i j
  rw [Matrix.smul_apply, hP_pow_mul_hX_pow, Fin.cast_val_eq_self]
  have c1 : ∀ i i₀ : Fin 3, (i - 1 = i₀ ↔ i = 1 + i₀) := by decide
  have c2 : ∀ i i₀ : Fin 3, (i - 1 - 1 = i₀ ↔ i = 2 + i₀) := by decide
  fin_cases j
  · simp [hcol0 i, add_comm]
  · simp [hcol1 i, c1 i i₀, add_comm, hb]
    split_ifs <;> ring
  · simp [hcol2 i, c2 i i₀, add_comm, hb]
    split_ifs <;> ring

end CFSG.HardMathSupport.Solomon.Coordinator
