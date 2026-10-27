module

public import CFSG.HardMathSupport.U4FF.ClassDatumNorm

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)

namespace Datum

section Matrices

variable {K : Type} [Field K] [CharP K 2]

theorem pmat_pA : (pmat pA : Matrix (Fin 4) (Fin 4) K) =
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pmat_apply, pA_zero, pA_one, pA_two, pA_three]

theorem pmat_pB : (pmat pB : Matrix (Fin 4) (Fin 4) K) =
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pmat_apply, pB_zero, pB_one, pB_two, pB_three]

theorem diagonal_vec (a b c d : K) :
    (diagonal ![a, b, c, d] : Matrix (Fin 4) (Fin 4) K) =
      !![a, 0, 0, 0; 0, b, 0, 0; 0, 0, c, 0; 0, 0, 0, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal_apply]

variable (n : ℕ)

theorem matrix_phi0 {u : K} (hu : u ≠ 0) :
    x0Mat n u * pmat pA = y0Mat n u⁻¹ * diagonal (tor0Vec n u) * x0Mat n u⁻¹ := by
  have hq : u ^ 2 ^ n ≠ 0 := pow_ne_zero _ hu
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pmat_pA, tor0Vec, diagonal_vec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x0Mat, y0Mat, Matrix.mul_apply, Fin.sum_univ_four, inv_pow] <;>
    field_simp <;> first | linear_combination (-1 : K) * hchar | linear_combination (-u) * hchar | linear_combination (-(u ^ 2 ^ n)) * hchar

theorem matrix_psi0 {u : K} (hu : u ≠ 0) :
    pmat pA * x0Mat n u * pmat pA =
      x0Mat n u⁻¹ * pmat pA * diagonal (tor0Vec n u) * x0Mat n u⁻¹ := by
  have hq : u ^ 2 ^ n ≠ 0 := pow_ne_zero _ hu
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pmat_pA, tor0Vec, diagonal_vec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x0Mat, Matrix.mul_apply, Fin.sum_univ_four, inv_pow] <;>
    field_simp <;> first | linear_combination (-1 : K) * hchar | linear_combination (-u) * hchar | linear_combination (-(u ^ 2 ^ n)) * hchar

theorem matrix_bruhat0 {u : K} (hu : u ≠ 0) :
    y0Mat n u⁻¹ = x0Mat n u * diagonal (tor0Vec n u) * pmat pA * x0Mat n u := by
  have hq : u ^ 2 ^ n ≠ 0 := pow_ne_zero _ hu
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pmat_pA, tor0Vec, diagonal_vec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x0Mat, y0Mat, Matrix.mul_apply, Fin.sum_univ_four, inv_pow] <;>
    field_simp <;> first | linear_combination (-1 : K) * hchar | linear_combination (-u) * hchar | linear_combination (-(u ^ 2 ^ n)) * hchar

theorem matrix_phi1 {u : K} (hu : u ≠ 0) :
    x1Mat u * pmat pB = y1Mat u⁻¹ * diagonal (tor1Vec u) * x1Mat u⁻¹ := by
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pmat_pB, tor1Vec, diagonal_vec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x1Mat, y1Mat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> first | linear_combination (-1 : K) * hchar | linear_combination (-u) * hchar | linear_combination (-(u ^ 2 ^ n)) * hchar

theorem matrix_psi1 {u : K} (hu : u ≠ 0) :
    pmat pB * x1Mat u * pmat pB =
      x1Mat u⁻¹ * pmat pB * diagonal (tor1Vec u) * x1Mat u⁻¹ := by
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pmat_pB, tor1Vec, diagonal_vec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x1Mat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> first | linear_combination (-1 : K) * hchar | linear_combination (-u) * hchar | linear_combination (-(u ^ 2 ^ n)) * hchar

theorem matrix_bruhat1 {u : K} (hu : u ≠ 0) :
    y1Mat u⁻¹ = x1Mat u * diagonal (tor1Vec u) * pmat pB * x1Mat u := by
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pmat_pB, tor1Vec, diagonal_vec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x1Mat, y1Mat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> first | linear_combination (-1 : K) * hchar | linear_combination (-u) * hchar | linear_combination (-(u ^ 2 ^ n)) * hchar

end Matrices

section Rank

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)

theorem gm_n_s0 : gm (nHom K n s0) = pmat pA := by rw [gm_nHom, permOf_s0]

theorem gm_n_s1 : gm (nHom K n s1) = pmat pB := by rw [gm_nHom, permOf_s1]

theorem rank0_phi (u : Kˣ) :
    x0 hK (u : K) * nHom K n s0 =
      y0 hK ((u⁻¹ : Kˣ) : K) * hTor0 hK u * x0 hK ((u⁻¹ : Kˣ) : K) := by
  apply eq_of_gm_eq
  rw [gm_mul, gm_mul, gm_mul, gm_x0 hK, gm_n_s0, gm_y0 hK, gm_hTor0 hK, gm_x0 hK,
    Units.val_inv_eq_inv_val]
  exact matrix_phi0 n u.ne_zero

theorem rank0_psi (u : Kˣ) :
    nHom K n s0 * x0 hK (u : K) * nHom K n s0 =
      x0 hK ((u⁻¹ : Kˣ) : K) * nHom K n s0 * hTor0 hK u * x0 hK ((u⁻¹ : Kˣ) : K) := by
  apply eq_of_gm_eq
  rw [gm_mul, gm_mul, gm_mul, gm_mul, gm_mul, gm_x0 hK, gm_n_s0, gm_hTor0 hK, gm_x0 hK,
    Units.val_inv_eq_inv_val]
  exact matrix_psi0 n u.ne_zero

theorem rank0_bruhat (u : Kˣ) :
    y0 hK ((u⁻¹ : Kˣ) : K) = x0 hK (u : K) * hTor0 hK u * nHom K n s0 * x0 hK (u : K) := by
  apply eq_of_gm_eq
  rw [gm_mul, gm_mul, gm_mul, gm_y0 hK, gm_x0 hK, gm_hTor0 hK, gm_n_s0,
    Units.val_inv_eq_inv_val]
  exact matrix_bruhat0 n u.ne_zero

theorem fq_coe_inv (u : (Fq K n)ˣ) :
    (((u⁻¹ : (Fq K n)ˣ) : Fq K n) : K) = ((u : Fq K n) : K)⁻¹ := by
  rw [Units.val_inv_eq_inv_val]
  rfl

theorem rank1_phi (u : (Fq K n)ˣ) :
    x1 hK (u : Fq K n) * nHom K n s1 =
      y1 hK ((u⁻¹ : (Fq K n)ˣ) : Fq K n) * hTor1 hK u * x1 hK ((u⁻¹ : (Fq K n)ˣ) : Fq K n) := by
  apply eq_of_gm_eq
  rw [gm_mul, gm_mul, gm_mul, gm_x1 hK, gm_n_s1, gm_y1 hK, gm_hTor1 hK, gm_x1 hK, fq_coe_inv]
  exact matrix_phi1 (fq_ne_zero u)

theorem rank1_psi (u : (Fq K n)ˣ) :
    nHom K n s1 * x1 hK (u : Fq K n) * nHom K n s1 =
      x1 hK ((u⁻¹ : (Fq K n)ˣ) : Fq K n) * nHom K n s1 * hTor1 hK u *
        x1 hK ((u⁻¹ : (Fq K n)ˣ) : Fq K n) := by
  apply eq_of_gm_eq
  rw [gm_mul, gm_mul, gm_mul, gm_mul, gm_mul, gm_x1 hK, gm_n_s1, gm_hTor1 hK, gm_x1 hK,
    fq_coe_inv]
  exact matrix_psi1 (fq_ne_zero u)

theorem rank1_bruhat (u : (Fq K n)ˣ) :
    y1 hK ((u⁻¹ : (Fq K n)ˣ) : Fq K n) =
      x1 hK (u : Fq K n) * hTor1 hK u * nHom K n s1 * x1 hK (u : Fq K n) := by
  apply eq_of_gm_eq
  rw [gm_mul, gm_mul, gm_mul, gm_y1 hK, gm_x1 hK, gm_hTor1 hK, gm_n_s1, fq_coe_inv]
  exact matrix_bruhat1 (fq_ne_zero u)

end Rank

end Datum

end CFSG.HardMathSupport.U4FF
