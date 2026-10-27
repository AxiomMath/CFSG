module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

section GraphField

variable (F : Type*) [Field F] [CharP F 2]

@[expose] noncomputable def graphFieldSL :
    SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F where
  toFun M := SpecialLinearGroup.map (frobenius F 2) (M⁻¹).transpose
  map_one' := by
    rw [inv_one]
    ext i j
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      SpecialLinearGroup.coe_transpose, SpecialLinearGroup.coe_one, Matrix.transpose_one,
      Matrix.one_apply]
    split_ifs <;> simp
  map_mul' M N := by
    rw [mul_inv_rev, ← map_mul]
    congr 1
    ext i j
    simp only [SpecialLinearGroup.coe_transpose, SpecialLinearGroup.coe_mul, transpose_mul]

variable {F}

theorem graphFieldSL_apply (M : SpecialLinearGroup (Fin 3) F) (i j : Fin 3) :
    (graphFieldSL F M : Matrix (Fin 3) (Fin 3) F) i j =
      ((M⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) j i ^ 2 := by
  simp only [graphFieldSL, MonoidHom.coe_mk, OneHom.coe_mk, SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, SpecialLinearGroup.coe_transpose,
    Matrix.transpose_apply, frobenius_def]

theorem graphFieldSL_graphFieldSL (hF : ∀ x : F, (x ^ 2) ^ 2 = x)
    (M : SpecialLinearGroup (Fin 3) F) : graphFieldSL F (graphFieldSL F M) = M := by
  ext i j
  rw [graphFieldSL_apply, ← map_inv, graphFieldSL_apply, inv_inv, hF]

end GraphField

@[expose] def SLThreeGraphFieldFixInput : Prop :=
  ∀ (F : Type) [Field F] [CharP F 2], Nat.card F = 4 →
    ∀ B : SpecialLinearGroup (Fin 3) F,
      (∀ y, B * graphFieldSL F (B * graphFieldSL F y * B⁻¹) * B⁻¹ = y) →
      27 ∣ Nat.card (((MulAut.conj B).toMonoidHom.comp (graphFieldSL F)).eqLocus
        (MonoidHom.id (SpecialLinearGroup (Fin 3) F)))

end CFSG.SeitzReduction.LinearPilot
