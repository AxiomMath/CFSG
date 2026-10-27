module

public import CFSG.LieType.SeitzGeneration.HeisLinearDefs
public import Mathlib.LinearAlgebra.Vandermonde

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

theorem heisShiftMat_entry {F : Type*} [Field F] {p : ℕ} (i j : Fin p) :
    heisShiftMat F p i j = if finRotate p i = j then 1 else 0 := by
  simp [heisShiftMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem finRotate_val_mod {p : ℕ} [NeZero p] (k : Fin p) :
    ((finRotate p k : Fin p) : ℕ) = ((k : ℕ) + 1) % p := by
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

theorem heisDiagMat_mul_heisShiftMat {F : Type*} [Field F] {p : ℕ} [NeZero p] (ω : F)
    (hω : ω ^ p = 1) :
    heisDiagMat ω * heisShiftMat F p = ω⁻¹ • (heisShiftMat F p * heisDiagMat ω) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne p)] at hω
    exact zero_ne_one hω
  ext i j
  simp only [heisDiagMat, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
    smul_eq_mul, heisShiftMat_entry]
  split_ifs with h
  · subst h
    have key : ω ^ ((finRotate p i : Fin p) : ℕ) = ω ^ (i : ℕ) * ω := by
      rw [finRotate_val_mod, ← pow_eq_pow_mod ((i : ℕ) + 1) hω, pow_succ]
    rw [key]
    field_simp
  · simp

theorem heisShiftMat_mul_heisFourierMat {F : Type*} [Field F] {p : ℕ} [NeZero p] {ζ : F}
    (hζ : ζ ^ p = 1) :
    heisShiftMat F p * heisFourierMat ζ = heisFourierMat ζ * Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ)) := by
  ext i j
  have hmod : Nat.ModEq p ((finRotate p i : Fin p) : ℕ) ((i : ℕ) + 1) := by
    rw [finRotate_val_mod]
    exact Nat.mod_modEq _ _
  have hmulmod : Nat.ModEq p (((finRotate p i : Fin p) : ℕ) * (j : ℕ))
      (((i : ℕ) + 1) * (j : ℕ)) :=
    Nat.ModEq.mul_right _ hmod
  have hpow : ζ ^ (((finRotate p i : Fin p) : ℕ) * (j : ℕ)) =
      ζ ^ (((i : ℕ) + 1) * (j : ℕ)) := by
    unfold Nat.ModEq at hmulmod
    rw [pow_eq_pow_mod (((finRotate p i : Fin p) : ℕ) * (j : ℕ)) hζ,
      pow_eq_pow_mod (((i : ℕ) + 1) * (j : ℕ)) hζ, hmulmod]
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, heisShiftMat_entry, heisFourierMat, Matrix.of_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hpow, add_mul, one_mul, pow_add]

theorem det_heisFourierMat_ne_zero {F : Type*} [Field F] {p : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    (heisFourierMat ζ : Matrix (Fin p) (Fin p) F).det ≠ 0 := by
  have hT : (heisFourierMat ζ : Matrix (Fin p) (Fin p) F) =
      (Matrix.vandermonde (fun j : Fin p => ζ ^ (j : ℕ)))ᵀ := by
    ext i j
    simp only [heisFourierMat, Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [← pow_mul, mul_comm]
  rw [hT, Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext (hζ.pow_inj a.isLt b.isLt hab)

theorem det_heisShiftMat (F : Type*) [Field F] {p : ℕ} (hp : Odd p) :
    (heisShiftMat F p).det = 1 := by
  obtain ⟨k, rfl⟩ := hp
  rw [heisShiftMat, Matrix.det_permutation, sign_finRotate]
  simp [pow_mul]

theorem det_heisDiagMat {F : Type*} [Field F] {p : ℕ} {ω : F} (hω : ω ^ p = 1) (hp : Odd p) :
    (heisDiagMat (p := p) ω).det = 1 := by
  obtain ⟨k, rfl⟩ := hp
  have hsum : ∑ i : Fin (2 * k + 1), (i : ℕ) = (2 * k + 1) * k := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) (2 * k + 1), Finset.sum_range_id,
      show 2 * k + 1 - 1 = 2 * k by omega,
      show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  simp only [heisDiagMat, Matrix.det_diagonal]
  rw [Finset.prod_pow_eq_pow_sum, hsum, pow_mul, hω, one_pow]

end CFSG.LieType.SeitzGeneration

end
