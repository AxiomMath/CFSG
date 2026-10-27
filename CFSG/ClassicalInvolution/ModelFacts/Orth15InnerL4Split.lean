module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4X

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4

open Matrix CFSG.ClassicalInvolution.WeakCT
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def scal4 (i : F) (hi : i ^ 4 = 1) : SL(4, F) :=
  ⟨i • 1, by simp [hi]⟩

theorem coe_scal4 (i : F) (hi : i ^ 4 = 1) :
    ((scal4 i hi : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = i • 1 := rfl

theorem scal4_mem_center (i : F) (hi : i ^ 4 = 1) : scal4 i hi ∈ Subgroup.center SL(4, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨i, by simpa using hi, ?_⟩
  rw [coe_scal4, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

@[expose] def Gm (i : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 1, 0; -i, 0, i, 0; 0, 1, 0, 1; 0, -i, 0, i]

theorem det_Gm {i : F} (hi : i * i = -1) : (Gm i).det = 4 := by
  simp [Gm, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination (-4) * hi

@[expose] noncomputable def Gel (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) : GL (Fin 4) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Gm i) (by
    rw [det_Gm hi]
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2)

theorem coe_Gel (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) :
    ((Gel h2 hi : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Gm i := rfl

theorem four_pow_of_sq {i : F} (hi : i * i = -1) : i ^ 4 = 1 := by
  linear_combination (i * i - 1) * hi

theorem Gm_mul_zx {i : F} (hi : i * i = -1) :
    Gm i * ((scal4 i (four_pow_of_sq hi) * x0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      ((u0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Gm i := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_scal4, coe_x0, coe_u0]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Gm, Matrix.mul_apply, Fin.sum_univ_four] <;> exact hi

@[expose] def dg (a d : F) (h : a * d = 1) : SL(2, F) :=
  ⟨!![a, 0; 0, d], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

@[expose] def up (b : F) : SL(2, F) := ⟨!![1, b; 0, 1], by simp⟩

theorem Gm_mul_t0 {i : F} (hi : i * i = -1) :
    Gm i * ((blk (dg i (-i) (by linear_combination (-1) * hi))
      (dg (-i) i (by linear_combination (-1) * hi)) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      ((t0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Gm i := by
  rw [coe_blk, coe_t0]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Gm, dg, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | exact hi | linear_combination (-1) * hi

theorem Gm_mul_U1 (i : F) :
    Gm i * ((blk (up 1) (up 1) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      ((U1 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Gm i := by
  rw [coe_blk, coe_U1]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Gm, up, Matrix.mul_apply, Fin.sum_univ_four]

theorem exists_layer_u0_of_split [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {i : F}
    (hi : i * i = -1) :
    ∃ Q : Subgroup SL(4, F), SLayer (u0 F) Q ∧ t0 F ∈ Q ∧ U1 F ∈ Q := by
  have hD : SLayer (scal4 i (four_pow_of_sq hi) * x0 F) (R0 F ⊔ R0' F) :=
    (slayer_x0 h2 h4).of_central_mul (scal4_mem_center i (four_pow_of_sq hi))
  set τ := slConjugation 4 F (Gel h2 hi) with hτ
  have hτu : τ (scal4 i (four_pow_of_sq hi) * x0 F) = u0 F :=
    slConj_eq_of_mul_eq (Gel h2 hi) (Gm_mul_zx hi)
  refine ⟨(R0 F ⊔ R0' F).map τ.toMonoidHom, ?_, ?_, ?_⟩
  · have := hD.map τ
    rwa [hτu] at this
  · exact ⟨_, blk_mem _ _, slConj_eq_of_mul_eq (Gel h2 hi) (Gm_mul_t0 hi)⟩
  · exact ⟨_, blk_mem _ _, slConj_eq_of_mul_eq (Gel h2 hi) (Gm_mul_U1 i)⟩

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
