module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix Polynomial

variable {K : Type} [Field K]

theorem cube_root_relation {ξ : K} (hξ1 : ξ ≠ 1) (hξ3 : ξ ^ 3 = 1) : ξ ^ 2 + ξ + 1 = 0 := by
  have h : (ξ - 1) * (ξ ^ 2 + ξ + 1) = 0 := by
    calc (ξ - 1) * (ξ ^ 2 + ξ + 1) = ξ ^ 3 - 1 := by ring
      _ = 0 := by rw [hξ3]; ring
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hξ1
  · exact h

theorem exists_eigenvector_cube {ξ : K} (hξ1 : ξ ≠ 1) (hξ3 : ξ ^ 3 = 1) (x : Matrix (Fin 3) (Fin 3) K)
    (hx3 : x ^ 3 = 1) :
    ∃ μ : K, (μ = 1 ∨ μ = ξ ∨ μ = ξ ^ 2) ∧ ∃ v : Fin 3 → K, v ≠ 0 ∧ x *ᵥ v = μ • v := by
  have h2 := cube_root_relation hξ1 hξ3
  have hpoly : (X - C (1 : K)) * (X - C ξ) * (X - C (ξ ^ 2)) = (X ^ 3 - 1 : K[X]) := by
    have e1 : (X - C (1 : K)) * (X - C ξ) * (X - C (ξ ^ 2)) =
        X ^ 3 - C (1 + ξ + ξ ^ 2) * X ^ 2 + C (ξ + ξ ^ 2 + ξ ^ 3) * X - C (ξ ^ 3) := by
      simp only [map_add, map_pow, map_one]; ring
    have e2 : (1 + ξ + ξ ^ 2 : K) = 0 := by linear_combination h2
    have e3 : (ξ + ξ ^ 2 + ξ ^ 3 : K) = 0 := by linear_combination h2 + hξ3
    rw [e1, e2, e3, hξ3]; simp
  have hmat : (x - (1 : K) • (1 : Matrix (Fin 3) (Fin 3) K)) * (x - ξ • (1 : Matrix (Fin 3) (Fin 3) K)) *
      (x - ξ ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K)) = 0 := by
    have := congrArg (Polynomial.aeval x) hpoly
    simp only [map_mul, map_sub, aeval_X, aeval_C, map_pow, map_one] at this
    rw [hx3] at this
    simpa [Algebra.algebraMap_eq_smul_one, _root_.smul_pow] using this
  have hdet : (x - (1 : K) • (1 : Matrix (Fin 3) (Fin 3) K)).det *
      (x - ξ • (1 : Matrix (Fin 3) (Fin 3) K)).det * (x - ξ ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K)).det = 0 := by
    rw [← det_mul, ← det_mul, hmat, det_zero]
  have key : ∀ μ : K, (x - μ • (1 : Matrix (Fin 3) (Fin 3) K)).det = 0 →
      ∃ v : Fin 3 → K, v ≠ 0 ∧ x *ᵥ v = μ • v := by
    intro μ hμ
    obtain ⟨v, hv, hv0⟩ := (exists_mulVec_eq_zero_iff).mpr hμ
    refine ⟨v, hv, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hv0
    exact hv0
  rcases mul_eq_zero.mp hdet with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨1, Or.inl rfl, by simpa using key 1 (by simpa using h)⟩
    · exact ⟨ξ, Or.inr (Or.inl rfl), key ξ h⟩
  · exact ⟨ξ ^ 2, Or.inr (Or.inr rfl), key _ h⟩

theorem heis_frame (ξ : K) (hξ1 : ξ ≠ 1) (hξ3 : ξ ^ 3 = 1) (x y : Matrix (Fin 3) (Fin 3) K)
    (hx3 : x ^ 3 = 1) (hyu : IsUnit y) (hxy : x * y = ξ • (y * x)) :
    ∃ (B : Matrix (Fin 3) (Fin 3) K) (lam : K), IsUnit B ∧ lam ≠ 0 ∧
      x * B = B * diagonal (fun i : Fin 3 => ξ ^ (i : ℕ) * lam) := by
  obtain ⟨μ, hμ, v₀, hv₀, hxv₀⟩ := exists_eigenvector_cube hξ1 hξ3 x hx3
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
  have hμ0 : μ ≠ 0 := by rcases hμ with rfl | rfl | rfl <;> simp [hξ0]
  have hxyi : ∀ i : ℕ, x * y ^ i = ξ ^ i • (y ^ i * x) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc x * y ^ (i + 1) = (x * y ^ i) * y := by rw [pow_succ, ← mul_assoc]
        _ = (ξ ^ i • (y ^ i * x)) * y := by rw [ih]
        _ = ξ ^ i • (y ^ i * (x * y)) := by rw [smul_mul_assoc, mul_assoc]
        _ = ξ ^ i • (y ^ i * (ξ • (y * x))) := by rw [hxy]
        _ = ξ ^ (i + 1) • (y ^ (i + 1) * x) := by
          rw [mul_smul_comm, smul_smul, ← mul_assoc, ← pow_succ y i, ← pow_succ ξ i]
  have hyui : ∀ i : ℕ, IsUnit (y ^ i) := fun i => hyu.pow i
  have hξord : orderOf ξ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hξ3 hξ1
  let μs : Fin 3 → K := fun i => ξ ^ (i : ℕ) * μ
  let vs : Fin 3 → (Fin 3 → K) := fun i => (y ^ (i : ℕ)) *ᵥ v₀
  have hxv : ∀ i : Fin 3, x *ᵥ vs i = μs i • vs i := by
    intro i
    show x *ᵥ ((y ^ (i : ℕ)) *ᵥ v₀) = (ξ ^ (i : ℕ) * μ) • ((y ^ (i : ℕ)) *ᵥ v₀)
    rw [mulVec_mulVec, hxyi, smul_mulVec, ← mulVec_mulVec, hxv₀, mulVec_smul, smul_smul]
  have hv0 : ∀ i : Fin 3, vs i ≠ 0 := by
    intro i h
    apply hv₀
    exact (Matrix.mulVec_injective_iff_isUnit.mpr (hyui i)) (by rw [mulVec_zero]; exact h)
  have hμs : Function.Injective μs := by
    intro i j h
    have h' : ξ ^ (i : ℕ) = ξ ^ (j : ℕ) := mul_right_cancel₀ hμ0 h
    exact Fin.ext (pow_injOn_Iio_orderOf (by rw [hξord]; exact i.2) (by rw [hξord]; exact j.2) h')
  have hli : LinearIndependent K vs := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.mulVecLin x) μs hμs vs ?_
    intro i
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨by simpa using hxv i, hv0 i⟩
  set B : Matrix (Fin 3) (Fin 3) K := (Matrix.of vs).transpose with hB
  have hBu : IsUnit B := by
    have hcol : B.col = vs := by
      funext j i
      simp [hB, Matrix.col_apply]
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]
    exact hli
  refine ⟨B, μ, hBu, hμ0, ?_⟩
  ext i j
  have h1 := congrFun (hxv j) i
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
  simp only [hB, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [h1]
  simp [μs, mul_comm]

end CFSG.GH74.GLS.Stage2.OddAut
