module

public import CFSG.ClassicalInvolution.Q3.TL4MF163L3B
public import CFSG.ClassicalInvolution.Q3.TL4MF163LU

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem eq_of_inv_aut [Finite K] (h2 : (2 : K) ≠ 0) (hτ : ∀ τ : K ≃+* K, τ * τ = 1 → τ = 1)
    {l : Kˣ} (hl : (l : K) * l = -1) (μ : Kˣ) {b : MulAut (projectiveSL 3 K)} (hb2 : b * b = 1)
    (hbc : b (proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) =
      proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l)))
    (hbσ : b * (conjAut 3 K (sigMat μ) * dualAut 3 K) =
      conjAut 3 K (sigMat μ) * dualAut 3 K * b) :
    b = 1 ∨ b = conjAut 3 K (Lemma41aL3.blk (-1)) := by
  obtain ⟨g, τ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 b
  interval_cases ε
  · rw [pow_zero, mul_one] at hb2 hbc hbσ ⊢
    have hττ : τ * τ = 1 := (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl _ _
      (by rw [conjAut_mul_fieldAut_mul] at hb2; exact hb2)).1
    obtain rfl := hτ τ hττ
    rw [map_one, mul_one] at hb2 hbc hbσ ⊢
    obtain ⟨h02, h12, h20, h21⟩ := block_of_fix h2 hl hbc
    have hdet := det_eq_of_comm μ ⟨h02, h12, h20, h21⟩ hbσ
    set M := (g : Matrix (Fin 3) (Fin 3) K) with hM
    have hdetM : M.det = M 2 2 * (M 2 2 * M 2 2) := by
      rw [Matrix.det_fin_three, h02, h12, h20, h21]
      linear_combination M 2 2 * hdet
    have hb₀ : M 2 2 ≠ 0 := fun h0 => by
      have : M.det = 0 := by rw [hdetM, h0, zero_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero this
    let B : Matrix (Fin 2) (Fin 2) K := (M 2 2)⁻¹ • !![M 0 0, M 0 1; M 1 0, M 1 1]
    have hBdet : B.det = 1 := by
      rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, hdet]
      field_simp
    let B' : GL (Fin 2) K := GeneralLinearGroup.mkOfDetNeZero B (by rw [hBdet]; exact one_ne_zero)
    have hB'det : (B' : Matrix (Fin 2) (Fin 2) K).det = 1 := hBdet
    have hg : g =
        GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (M 2 2) hb₀) * Lemma41aL3.blk B' := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Lemma41aL3.coe_blk, hB'det, inv_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [B', B, Lemma41aL3.blkMat, ← hM, h02, h12, h20, h21, hb₀]
    have hcb : conjAut 3 K g = conjAut 3 K (Lemma41aL3.blk B') := by
      rw [hg, map_mul, conjAut_scalar, one_mul]
    rw [hcb] at hb2 ⊢
    rw [← map_mul, ← map_mul] at hb2
    obtain ⟨κ, hκ⟩ := (conjAut_eq_one_iff (le_refl 3) _).1 hb2
    have hκ' := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hκ
    simp only [Lemma41aL3.coe_blk, GeneralLinearGroup.coe_scalar] at hκ'
    have hκ1 : (κ : K) = 1 := by
      have e := congrFun (congrFun hκ' 2) 2
      simp [Lemma41aL3.blkMat, Matrix.det_mul, hB'det] at e
      exact e.symm
    have hBB : B' * B' = 1 := Units.ext (by
      rw [Units.val_mul, Units.val_one]
      ext i j
      have e := congrFun (congrFun hκ' i.castSucc) j.castSucc
      fin_cases i <;> fin_cases j <;> simpa [Lemma41aL3.blkMat, hκ1] using e)
    obtain ⟨c, hc⟩ := MF163.exists_scalar_of_mul_self h2 (Units.ext (by
      rw [GeneralLinearGroup.val_det_apply, hB'det, Units.val_one])) hBB
    have hc2 : (c : K) * c = 1 := by
      have e := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) hBB
      simp only [hc, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_one] at e
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using e
    rcases mul_self_eq_one_iff.mp hc2 with h1 | h1
    · left
      have : B' = 1 := by rw [hc]; exact Units.ext (by
        rw [GeneralLinearGroup.coe_scalar, h1, map_one, Units.val_one])
      rw [this, map_one, map_one]
    · right
      have : B' = -1 := by rw [hc]; exact Units.ext (by
        rw [GeneralLinearGroup.coe_scalar, h1, Units.val_neg, Units.val_one, map_neg, map_one])
      rw [this]
  · rw [pow_one] at hb2 hbc hbσ ⊢
    have hττ : τ * τ = 1 := (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl _ _
      (by rw [← sq, sq_conjAut_fieldAut_dualAut] at hb2; exact hb2)).1
    obtain rfl := hτ τ hττ
    rw [map_one, mul_one] at hbc
    exact absurd hbc (not_fix_dual h2 hl g)

end CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
