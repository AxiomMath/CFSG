module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

variable {L : Type} [Field L]

@[expose] def hfm {n : ℕ} (τ : L ≃+* L) (x y : Fin n → L) : L := ∑ j, τ (x j) * y j

@[expose] def adjM {n : ℕ} (τ : L ≃+* L) (X : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  (X.map τ)ᵀ

variable {n : ℕ} (τ : L ≃+* L)

theorem hfm_add_left (x x' y : Fin n → L) : hfm τ (x + x') y = hfm τ x y + hfm τ x' y := by
  simp [hfm, add_mul, Finset.sum_add_distrib]

theorem hfm_add_right (x y y' : Fin n → L) : hfm τ x (y + y') = hfm τ x y + hfm τ x y' := by
  simp [hfm, mul_add, Finset.sum_add_distrib]

theorem hfm_smul_left (c : L) (x y : Fin n → L) : hfm τ (c • x) y = τ c * hfm τ x y := by
  simp [hfm, Finset.mul_sum, mul_assoc]

theorem hfm_smul_right (c : L) (x y : Fin n → L) : hfm τ x (c • y) = c * hfm τ x y := by
  simp [hfm, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem adjM_mul (X Y : Matrix (Fin n) (Fin n) L) :
    adjM τ (X * Y) = adjM τ Y * adjM τ X := by
  simp [adjM, Matrix.map_mul, Matrix.transpose_mul]

theorem adjM_add (X Y : Matrix (Fin n) (Fin n) L) : adjM τ (X + Y) = adjM τ X + adjM τ Y := by
  simp [adjM, Matrix.map_add, Matrix.transpose_add]

theorem adjM_one : adjM τ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  simp [adjM, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]

theorem adjM_smul (c : L) (X : Matrix (Fin n) (Fin n) L) :
    adjM τ (c • X) = τ c • adjM τ X := by
  ext i j
  simp [adjM, Matrix.map_apply]

theorem adjM_adjM (hτ : ∀ x, τ (τ x) = x) (X : Matrix (Fin n) (Fin n) L) :
    adjM τ (adjM τ X) = X := by
  ext i j
  simp [adjM, Matrix.map_apply, hτ]

theorem adjM_pow (X : Matrix (Fin n) (Fin n) L) (k : ℕ) :
    adjM τ (X ^ k) = (adjM τ X) ^ k := by
  induction k with
  | zero => simp [adjM_one]
  | succ k ih => rw [pow_succ, adjM_mul, ih, pow_succ']

theorem hfm_mulVec (X : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) :
    hfm τ (X *ᵥ x) y = hfm τ x (adjM τ X *ᵥ y) := by
  simp only [hfm, Matrix.mulVec, dotProduct, adjM, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hfm_symm (hτ : ∀ x, τ (τ x) = x) (x y : Fin n → L) :
    τ (hfm τ x y) = hfm τ y x := by
  simp only [hfm, map_sum, map_mul, hτ]
  refine Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem hfm_nondeg (x : Fin n → L) (h : ∀ y, hfm τ x y = 0) : x = 0 := by
  funext j
  have := h (Pi.single j 1)
  simp only [hfm, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at this
  simpa using this

theorem adjM_aeval (hτ : ∀ x, τ (τ x) = x) (s : Matrix (Fin n) (Fin n) L) (p : L[X]) :
    adjM τ (aeval s p) = aeval (adjM τ s) (p.map (τ : L →+* L)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, adjM_add, hp, hq, Polynomial.map_add, map_add]
  | monomial k c =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul,
      adjM_smul, adjM_pow]
    simp

theorem adjM_eq_pow (hτ : ∀ x, τ (τ x) = x) {m : ℕ} (hm : 0 < m) (s : Matrix (Fin n) (Fin n) L)
    (hsm : s ^ m = 1) (hs : adjM τ s * s = 1) : adjM τ s = s ^ (m - 1) := by
  have h1 : s * s ^ (m - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hm, hsm]
  calc adjM τ s = adjM τ s * (s * s ^ (m - 1)) := by rw [h1, mul_one]
    _ = (adjM τ s * s) * s ^ (m - 1) := (mul_assoc _ _ _).symm
    _ = s ^ (m - 1) := by rw [hs, one_mul]

@[expose] noncomputable def starP (m : ℕ) (p : L[X]) : L[X] := (p.map (τ : L →+* L)).comp (X ^ (m - 1))

theorem adjM_aeval_eq_aeval_starP (hτ : ∀ x, τ (τ x) = x) {m : ℕ} (hm : 0 < m)
    (s : Matrix (Fin n) (Fin n) L) (hsm : s ^ m = 1) (hs : adjM τ s * s = 1) (p : L[X]) :
    adjM τ (aeval s p) = aeval s (starP τ m p) := by
  rw [adjM_aeval τ hτ, adjM_eq_pow τ hτ hm s hsm hs, starP, Polynomial.aeval_comp, aeval_X_pow]

theorem hfm_sum_right {ι : Type*} (t : Finset ι) (x : Fin n → L) (v : ι → Fin n → L) :
    hfm τ x (∑ i ∈ t, v i) = ∑ i ∈ t, hfm τ x (v i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [hfm]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hfm_add_right, ih]

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
