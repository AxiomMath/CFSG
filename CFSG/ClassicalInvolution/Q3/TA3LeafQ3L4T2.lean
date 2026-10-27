module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTL4

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

namespace Q3L4

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL TBlocks HBlocks
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def swapM : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem det_swapM : (swapM : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [swapM, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem swapM_mul_swapM : (swapM : Matrix (Fin 4) (Fin 4) K) * swapM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapM_mul_bd (a b : Matrix (Fin 2) (Fin 2) K) : swapM * bd a b = bd b a * swapM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM, bd, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapM_mul_X1 : (swapM : Matrix (Fin 4) (Fin 4) K) * X1 1 = (-1 : K) • (X1 1 * swapM) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM, X1, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def cP4 (P : GL (Fin 4) K) (Y : SL(4, K)) : Matrix (Fin 4) (Fin 4) K :=
  (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (Y : Matrix (Fin 4) (Fin 4) K) * P

theorem cP4_mul (P : GL (Fin 4) K) (Y Z : SL(4, K)) : cP4 P (Y * Z) = cP4 P Y * cP4 P Z := by
  have hPP' : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [cP4, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) K), hPP', Matrix.one_mul]

theorem cP4_one (P : GL (Fin 4) K) : cP4 P 1 = 1 := by
  rw [cP4, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel,
    Units.val_one]

theorem val_eq_cP4 (P : GL (Fin 4) K) (Y : SL(4, K)) :
    (Y : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * cP4 P Y * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
  have hPP' : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [cP4]
  simp only [← Matrix.mul_assoc, hPP', Matrix.one_mul]
  rw [Matrix.mul_assoc, hPP', Matrix.mul_one]

theorem eq_of_cP4_eq (P : GL (Fin 4) K) {Y Z : SL(4, K)} (h : cP4 P Y = cP4 P Z) : Y = Z :=
  Subtype.ext (by rw [val_eq_cP4 P Y, val_eq_cP4 P Z, h])

theorem cP4_bdHom (P : GL (Fin 4) K) (x : SL(2, K) × SL(2, K)) :
    cP4 P (bdHom P x) = bd (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin 2) (Fin 2) K) := by
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [cP4, coe_bdHom]
  simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  rw [Matrix.mul_assoc, hPP, Matrix.mul_one]

theorem cP4_bdHom_mk (P : GL (Fin 4) K) (a b : SL(2, K)) :
    cP4 P (bdHom P (a, b)) = bd (a : Matrix (Fin 2) (Fin 2) K) (b : Matrix (Fin 2) (Fin 2) K) :=
  cP4_bdHom P (a, b)

theorem cP4_X {P : GL (Fin 4) K} {X : SL(4, K)}
    (hXP : (X : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) : cP4 P X = X1 1 := by
  rw [cP4, Matrix.mul_assoc, hXP, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul]

theorem proj_eq_of_smul {A B : SL(4, K)} {c : K} (hc : c ≠ 0)
    (h : (B : Matrix (Fin 4) (Fin 4) K) = c • (A : Matrix (Fin 4) (Fin 4) K)) :
    proj 4 K A = proj 4 K B := by
  rw [proj_eq_proj_iff, mem_scalars]
  refine ⟨Units.mk0 c hc, Units.ext ?_, ?_⟩
  · have hd := congrArg Matrix.det h
    rw [det_smul, B.2, A.2, mul_one, Fintype.card_fin] at hd
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact hd.symm
  · rw [Matrix.SpecialLinearGroup.coe_mul, h, Matrix.mul_smul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Units.val_mk0, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]

@[expose] noncomputable def swP (P : GL (Fin 4) K) : SL(4, K) :=
  ⟨(P : Matrix (Fin 4) (Fin 4) K) * swapM * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K), by
    rw [det_mul, det_mul, det_swapM, mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, det_one]⟩

theorem cP4_swP (P : GL (Fin 4) K) : cP4 P (swP P) = swapM := by
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  change (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((P : Matrix (Fin 4) (Fin 4) K) * swapM *
    (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K) = swapM
  simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  rw [Matrix.mul_assoc, hPP, Matrix.mul_one]

theorem swP_mul_swP (P : GL (Fin 4) K) : swP P * swP P = 1 :=
  eq_of_cP4_eq P (by rw [cP4_mul, cP4_swP, swapM_mul_swapM, cP4_one])

theorem swP_conj (P : GL (Fin 4) K) (a b : SL(2, K)) :
    swP P * bdHom P (a, b) * swP P = bdHom P (b, a) :=
  eq_of_cP4_eq P (by
    rw [cP4_mul, cP4_mul, cP4_swP, cP4_bdHom, cP4_bdHom, swapM_mul_bd, Matrix.mul_assoc,
      swapM_mul_swapM, Matrix.mul_one])

theorem val_swP_mul_X {P : GL (Fin 4) K} {X : SL(4, K)}
    (hXP : (X : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) :
    ((swP P * X : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      (-1 : K) • ((X * swP P : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) := by
  rw [val_eq_cP4 P (swP P * X), val_eq_cP4 P (X * swP P), cP4_mul, cP4_mul, cP4_swP, cP4_X hXP,
    swapM_mul_X1, Matrix.mul_smul, Matrix.smul_mul]

theorem proj_swP_comm {P : GL (Fin 4) K} {X : SL(4, K)}
    (hXP : (X : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) :
    proj 4 K (swP P) * proj 4 K X = proj 4 K X * proj 4 K (swP P) := by
  rw [← map_mul, ← map_mul]
  exact (proj_eq_of_smul (neg_ne_zero.mpr one_ne_zero) (val_swP_mul_X hXP)).symm

end Q3L4

end CFSG.ClassicalInvolution.Q3.TA3
