module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

variable {F : Type*} [Field F]

@[expose] def fixSL3 (σ : F ≃+* F) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) where
  carrier := {g | ∀ i j, σ ((g : Matrix (Fin 3) (Fin 3) F) i j) = (g : Matrix (Fin 3) (Fin 3) F) i j}
  one_mem' := by
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_one]
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  mul_mem' := by
    intro a b ha hb i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, map_sum, map_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [ha i k, hb k j]
  inv_mem' := by
    intro a ha i j
    simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    fin_cases i <;> fin_cases j <;> simp [ha _ _]

@[expose] def conjGL3 (h : Matrix.GeneralLinearGroup (Fin 3) F) :
    Matrix.SpecialLinearGroup (Fin 3) F →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun g := ⟨(h : Matrix (Fin 3) (Fin 3) F) * g * ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F),
    by
      rw [Matrix.det_mul, Matrix.det_mul, g.prop, mul_one, ← Matrix.det_mul, Units.mul_inv,
        Matrix.det_one]⟩
  map_one' := by
    ext i j
    simp
  map_mul' := by
    intro a b
    apply Subtype.ext
    show (h : Matrix (Fin 3) (Fin 3) F) * ((a : Matrix (Fin 3) (Fin 3) F) * b) *
        ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (h : Matrix (Fin 3) (Fin 3) F) * a *
          ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((h : Matrix (Fin 3) (Fin 3) F) * b *
          ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    have hinv : ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (h : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      (h : Matrix (Fin 3) (Fin 3) F), hinv, Matrix.one_mul]

@[expose] def SL3SubfieldJoin : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (σ : F ≃+* F), orderOf σ = 3 →
    ∀ h : Matrix.GeneralLinearGroup (Fin 3) F,
      (¬ ∃ c : F, c ≠ 0 ∧ ∀ i j, σ (c * (h : Matrix (Fin 3) (Fin 3) F) i j) =
        c * (h : Matrix (Fin 3) (Fin 3) F) i j) →
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ≤
        fixSL3 σ ⊔ (fixSL3 σ).map (conjGL3 h)

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
