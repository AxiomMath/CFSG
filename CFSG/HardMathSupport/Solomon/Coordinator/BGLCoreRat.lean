module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreBasic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem conjGL3_tv (h : GL (Fin 3) F) {x φ : Fin 3 → F} (hxφ : φ ⬝ᵥ x = 0) :
    conjGL3 h (tv x φ) =
      tv ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ x) (φ ᵥ* ((h⁻¹ : GL (Fin 3) F) : Matrix _ _ F)) := by
  have hdot : (φ ᵥ* ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ⬝ᵥ
      ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = 0 := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec, hxφ]
  apply Subtype.ext
  rw [conjGL3_coe, coe_tv hxφ, coe_tv hdot, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    coe_mul_inv, mul_vecMulVec, vecMulVec_mul]

theorem tv_mem_fixSL3 {x φ : Fin 3 → F} (hxφ : φ ⬝ᵥ x = 0) (hx : IsRat σ x) (hφ : IsRat σ φ) :
    tv x φ ∈ fixSL3 σ := by
  intro i j
  rw [coe_tv hxφ, Matrix.add_apply, vecMulVec_apply, map_add, map_mul, hx i, hφ j,
    isRatM_one i j]

theorem conj_tv_mem_joinH (h : GL (Fin 3) F) {x φ : Fin 3 → F} (hxφ : φ ⬝ᵥ x = 0)
    (hx : IsRat σ x) (hφ : IsRat σ φ) :
    tv ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ x) (φ ᵥ* ((h⁻¹ : GL (Fin 3) F) : Matrix _ _ F)) ∈
      joinH σ h := by
  rw [← conjGL3_tv h hxφ]
  exact Subgroup.mem_sup_right ⟨_, tv_mem_fixSL3 hxφ hx hφ, rfl⟩

theorem tv_col2 (x : Fin 3 → F) (hx : x 2 = 0) :
    tv x (Pi.single 2 1) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (x 0) *
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (x 1) := by
  have hd : (Pi.single 2 (1 : F) : Fin 3 → F) ⬝ᵥ x = 0 := by
    simp [dotProduct, Fin.sum_univ_three, hx]
  apply Subtype.ext
  rw [coe_tv hd, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      vecMulVec_apply, hx]

theorem tv_row0 (y : Fin 3 → F) (hy : y 0 = 0) :
    tv (Pi.single 0 1) y =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (y 1) *
        SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (y 2) := by
  have hd : y ⬝ᵥ (Pi.single 0 (1 : F) : Fin 3 → F) = 0 := by
    simp [dotProduct, Fin.sum_univ_three, hy]
  apply Subtype.ext
  rw [coe_tv hd, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      vecMulVec_apply, hy]

theorem exists_ratGL_col0 {v : Fin 3 → F} (hv : IsRat σ v) (h0 : v ≠ 0) :
    ∃ m ∈ ratGL σ, (m : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = v := by
  have hcol : ∀ M : Matrix (Fin 3) (Fin 3) F, (∀ i, M i 0 = v i) → M *ᵥ Pi.single 0 1 = v := by
    intro M hM
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hM]
  by_cases h0' : v 0 ≠ 0
  · have hd : (!![v 0, 0, 0; v 1, 1, 0; v 2, 0, 1] : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      simpa [Matrix.det_fin_three] using h0'
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_, hcol _ ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, hv _]
    · intro i
      fin_cases i <;> rfl
  by_cases h1 : v 1 ≠ 0
  · have hd : (!![v 0, 1, 0; v 1, 0, 0; v 2, 0, 1] : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      simpa [Matrix.det_fin_three] using h1
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_, hcol _ ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, hv _]
    · intro i
      fin_cases i <;> rfl
  · have h2 : v 2 ≠ 0 := by
      intro h2
      apply h0
      funext i
      fin_cases i
      · exact not_not.mp h0'
      · exact not_not.mp h1
      · exact h2
    have hd : (!![v 0, 1, 0; v 1, 0, 1; v 2, 0, 0] : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      simpa [Matrix.det_fin_three] using h2
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_, hcol _ ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, hv _]
    · intro i
      fin_cases i <;> rfl

theorem exists_ratGL_row2 {b : Fin 3 → F} (hb : IsRat σ b) (h0 : b ≠ 0) :
    ∃ a ∈ ratGL σ, Pi.single 2 1 ᵥ* (a : Matrix (Fin 3) (Fin 3) F) = b := by
  have hrow : ∀ M : Matrix (Fin 3) (Fin 3) F, (∀ j, M 2 j = b j) → Pi.single 2 1 ᵥ* M = b := by
    intro M hM
    funext j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, hM]
  by_cases h2 : b 2 ≠ 0
  · have hd : (!![1, 0, 0; 0, 1, 0; b 0, b 1, b 2] : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      simpa [Matrix.det_fin_three] using h2
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_, hrow _ ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, hb _]
    · intro j
      fin_cases j <;> rfl
  by_cases h1 : b 1 ≠ 0
  · have hd : (!![1, 0, 0; 0, 0, 1; b 0, b 1, b 2] : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      simpa [Matrix.det_fin_three] using h1
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_, hrow _ ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, hb _]
    · intro j
      fin_cases j <;> rfl
  · have h0' : b 0 ≠ 0 := by
      intro h0'
      apply h0
      funext i
      fin_cases i
      · exact h0'
      · exact not_not.mp h1
      · exact not_not.mp h2
    have hd : (!![0, 1, 0; 0, 0, 1; b 0, b 1, b 2] : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      simpa [Matrix.det_fin_three] using h0'
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_, hrow _ ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, hb _]
    · intro j
      fin_cases j <;> rfl

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
