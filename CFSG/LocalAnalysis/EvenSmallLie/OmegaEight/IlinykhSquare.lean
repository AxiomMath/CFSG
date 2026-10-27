module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

public section

namespace CFSG.EvenSmallLie.OmegaEight

open Polynomial Matrix

theorem charmatrix_mul_charmatrix_neg {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    {y : Matrix n n K} (hy : y * y = -1) :
    charmatrix y * charmatrix (-y) = scalar n (X ^ 2 + 1 : K[X]) := by
  have hcomm : Commute (scalar n (X : K[X])) ((C : K →+* K[X]).mapMatrix y) :=
    scalar_commute _ (fun r => Commute.all _ _) _
  have hyy : (C : K →+* K[X]).mapMatrix y * (C : K →+* K[X]).mapMatrix y = -1 := by
    rw [← map_mul, hy, map_neg, map_one]
  simp only [charmatrix, map_neg, sub_neg_eq_add]
  rw [sub_mul, mul_add, mul_add, hcomm.eq, hyy, ← map_mul (scalar n), map_add (scalar n),
    map_one]
  rw [sq]
  abel

theorem det_eq_one_of_mul_self_eq_neg_one {K : Type*} [Field K] {n : Type*} [Fintype n]
    [DecidableEq n] (hK : ∀ a : K, a * a ≠ -1) {y : Matrix n n K} (hy : y * y = -1) :
    y.det = 1 := by
  set p : K[X] := X ^ 2 + C 1 with hp
  have hpmonic : p.Monic := monic_X_pow_add_C 1 two_ne_zero
  have hpdeg : p.natDegree = 2 := natDegree_X_pow_add_C (R := K)
  have hpirr : Irreducible p := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hpdeg]
      decide
    · intro a ha
      apply hK a
      have h := ha.eq_zero
      simp only [hp, eval_add, eval_pow, eval_X, eval_C] at h
      rw [← sq]
      exact eq_neg_of_add_eq_zero_left h
  have hpprime : Prime p := hpirr.prime
  have hdvd : y.charpoly ∣ p ^ Fintype.card n := by
    refine ⟨(-y).charpoly, ?_⟩
    rw [Matrix.charpoly, Matrix.charpoly, ← det_mul, charmatrix_mul_charmatrix_neg hy,
      scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, hp, map_one]
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hpprime _).mp hdvd
  have heq : y.charpoly = p ^ i := eq_of_monic_of_associated (charpoly_monic y) (hpmonic.pow i) hi
  have hdim : Fintype.card n = 2 * i := by
    rw [← charpoly_natDegree_eq_dim y, heq, natDegree_pow, hpdeg, mul_comm]
  rw [det_eq_sign_charpoly_coeff, heq, coeff_zero_eq_eval_zero, eval_pow, hdim, pow_mul]
  simp [hp]

end CFSG.EvenSmallLie.OmegaEight
