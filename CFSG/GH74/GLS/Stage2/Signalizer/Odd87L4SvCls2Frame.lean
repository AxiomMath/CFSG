module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLa

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open scoped MatrixGroups commutatorElement

section Frame

variable {F : Type} [Field F]

@[expose] noncomputable def stdGL (c : Fˣ) : GL (Fin 4) F :=
  ⟨stdN (c : F), ((c⁻¹ : Fˣ) : F) • stdN (c : F),
    by rw [Matrix.mul_smul, stdN_mul_stdN, smul_smul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul],
    by rw [Matrix.smul_mul, stdN_mul_stdN, smul_smul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul]⟩

theorem coe_stdGL (c : Fˣ) :
    ((stdGL c : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = stdN (c : F) := rfl

theorem coe_stdGL_inv (c : Fˣ) :
    (((stdGL c : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((c⁻¹ : Fˣ) : F) • stdN (c : F) := rfl

theorem coe_scalar_gl (c : Fˣ) :
    ((GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]

theorem exists_normal_form {A : GL (Fin 4) F} {c : Fˣ}
    (hA : A * A = GeneralLinearGroup.scalar (Fin 4) c) (hc : ¬ IsSquare (c : F)) :
    ∃ P : GL (Fin 4) F,
      conjAut 4 F (stdGL c) = conjAut 4 F P * conjAut 4 F A * (conjAut 4 F P)⁻¹ := by
  have hAm : (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) =
      (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
    have := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) hA
    rwa [Units.val_mul, coe_scalar_gl] at this
  obtain ⟨Pm, hPu, hP⟩ := exists_mul_eq_mul_stdN hc hAm
  set Pg : GL (Fin 4) F := Matrix.nonsingInvUnit Pm hPu with hPg
  have hPgm : (Pg : Matrix (Fin 4) (Fin 4) F) = Pm := rfl
  have h1 : A * Pg = Pg * stdGL c := Units.ext (by
    simp only [Units.val_mul, hPgm, coe_stdGL]
    exact hP)
  refine ⟨Pg⁻¹, ?_⟩
  have h2 : stdGL c = Pg⁻¹ * A * Pg := by
    rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
  have h3 : (conjAut 4 F Pg⁻¹)⁻¹ = conjAut 4 F Pg := by rw [← map_inv, inv_inv]
  rw [h3, ← map_mul, ← map_mul, ← h2]

@[expose] def commSub (c : F) : Subgroup SL(4, F) where
  carrier := {g | (g : Matrix (Fin 4) (Fin 4) F) * stdN c = stdN c * (g : Matrix (Fin 4) (Fin 4) F)}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show ((a * b : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * stdN c =
      stdN c * ((a * b : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, (hb : _ * stdN c = _),
      ← Matrix.mul_assoc, (ha : _ * stdN c = _), Matrix.mul_assoc]
  inv_mem' := fun {a} ha => by
    show ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * stdN c =
      stdN c * ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
    have h1 : ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (a : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (a : Matrix (Fin 4) (Fin 4) F) * ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have ha' : (a : Matrix (Fin 4) (Fin 4) F) * stdN c = stdN c * (a : Matrix (Fin 4) (Fin 4) F) := ha
    calc ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * stdN c
        = ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * stdN c *
            ((a : Matrix (Fin 4) (Fin 4) F) * ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)) := by
          rw [h2, Matrix.mul_one]
      _ = ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
            (stdN c * (a : Matrix (Fin 4) (Fin 4) F)) *
            ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
          simp only [Matrix.mul_assoc]
      _ = ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
            ((a : Matrix (Fin 4) (Fin 4) F) * stdN c) *
            ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by rw [ha']
      _ = stdN c * ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem mem_commSub {c : F} {g : SL(4, F)} :
    g ∈ commSub c ↔
      (g : Matrix (Fin 4) (Fin 4) F) * stdN c = stdN c * (g : Matrix (Fin 4) (Fin 4) F) :=
  Iff.rfl

theorem proj_mem_fixSub_of_mem_commSub (c : Fˣ) {g : SL(4, F)} (hg : g ∈ commSub (c : F)) :
    proj 4 F g ∈ fixSub (conjAut 4 F (stdGL c)) := by
  show conjAut 4 F (stdGL c) (proj 4 F g) = proj 4 F g
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, coe_stdGL,
    coe_stdGL_inv]
  have hg' : (g : Matrix (Fin 4) (Fin 4) F) * stdN (c : F) =
      stdN (c : F) * (g : Matrix (Fin 4) (Fin 4) F) := hg
  calc stdN (c : F) * (g : Matrix (Fin 4) (Fin 4) F) * (((c⁻¹ : Fˣ) : F) • stdN (c : F))
      = (g : Matrix (Fin 4) (Fin 4) F) * stdN (c : F) * (((c⁻¹ : Fˣ) : F) • stdN (c : F)) := by
        rw [hg']
    _ = (g : Matrix (Fin 4) (Fin 4) F) * (((c⁻¹ : Fˣ) : F) • (stdN (c : F) * stdN (c : F))) := by
        rw [Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_smul]
    _ = (g : Matrix (Fin 4) (Fin 4) F) := by
        rw [stdN_mul_stdN, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul,
          Matrix.mul_one]

@[expose] def uMat (c a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, a, b * c; 0, 1, b, a; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def lMat (c a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; a, b * c, 1, 0; b, a, 0, 1]

theorem det_uMat (c a b : F) : (uMat c a b).det = 1 := by
  rw [uMat, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem det_lMat (c a b : F) : (lMat c a b).det = 1 := by
  rw [lMat, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem uMat_zero (c : F) : uMat c 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uMat_mul (c a b a' b' : F) : uMat c a b * uMat c a' b' = uMat c (a + a') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

theorem lMat_mul (c a b a' b' : F) : lMat c a b * lMat c a' b' = lMat c (a + a') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lMat, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

theorem uMat_comm (c a b : F) : uMat c a b * stdN c = stdN c * uMat c a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, stdN, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

theorem lMat_comm (c a b : F) : lMat c a b * stdN c = stdN c * lMat c a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lMat, stdN, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

@[expose] def uSL (c a b : F) : SL(4, F) := ⟨uMat c a b, det_uMat c a b⟩

@[expose] def lSL (c a b : F) : SL(4, F) := ⟨lMat c a b, det_lMat c a b⟩

theorem coe_uSL (c a b : F) :
    ((uSL c a b : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = uMat c a b := rfl

theorem coe_lSL (c a b : F) :
    ((lSL c a b : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = lMat c a b := rfl

theorem uSL_mem_commSub (c a b : F) : uSL c a b ∈ commSub c := uMat_comm c a b

theorem lSL_mem_commSub (c a b : F) : lSL c a b ∈ commSub c := lMat_comm c a b

theorem uSL_mul (c a b a' b' : F) : uSL c a b * uSL c a' b' = uSL c (a + a') (b + b') :=
  Subtype.ext (uMat_mul c a b a' b')

theorem lSL_mul (c a b a' b' : F) : lSL c a b * lSL c a' b' = lSL c (a + a') (b + b') :=
  Subtype.ext (lMat_mul c a b a' b')

theorem uSL_zero (c : F) : uSL c 0 0 = 1 := Subtype.ext (uMat_zero c)

theorem uSL_inv (c a b : F) : (uSL c a b)⁻¹ = uSL c (-a) (-b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [uSL_mul, add_neg_cancel, add_neg_cancel, uSL_zero]

theorem uMat_mulVec_zero (c a b : F) (w : Fin 4 → F) :
    (uMat c a b *ᵥ w) 0 = w 0 + a * w 2 + b * c * w 3 := by
  simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem uMat_mulVec_one (c a b : F) (w : Fin 4 → F) :
    (uMat c a b *ᵥ w) 1 = w 1 + b * w 2 + a * w 3 := by
  simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem uMat_mulVec_two (c a b : F) (w : Fin 4 → F) : (uMat c a b *ᵥ w) 2 = w 2 := by
  simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem uMat_mulVec_three (c a b : F) (w : Fin 4 → F) : (uMat c a b *ᵥ w) 3 = w 3 := by
  simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem lMat_mulVec_zero (c a b : F) (w : Fin 4 → F) : (lMat c a b *ᵥ w) 0 = w 0 := by
  simp [lMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem lMat_mulVec_one (c a b : F) (w : Fin 4 → F) : (lMat c a b *ᵥ w) 1 = w 1 := by
  simp [lMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem lMat_mulVec_two (c a b : F) (w : Fin 4 → F) :
    (lMat c a b *ᵥ w) 2 = a * w 0 + b * c * w 1 + w 2 := by
  simp [lMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem lMat_mulVec_three (c a b : F) (w : Fin 4 → F) :
    (lMat c a b *ᵥ w) 3 = b * w 0 + a * w 1 + w 3 := by
  simp [lMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

end Frame

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
