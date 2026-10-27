module

public import CFSG.ClassicalInvolution.Phan.PhanB14Nu

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {F : Type} [Field F] [Algebra F K]

@[expose] def nuMat (c d α₁ α₂ β₁ β₂ : F) : Matrix (Fin 2) (Fin 2) F :=
  !![α₁ + β₁ * c - β₂ * d, -α₂ + β₁ * d + β₂ * c; α₂ + β₁ * d + β₂ * c, α₁ - β₁ * c + β₂ * d]

theorem det_nuMat (c d α₁ α₂ β₁ β₂ : F) :
    (nuMat c d α₁ α₂ β₁ β₂).det =
      α₁ * α₁ + α₂ * α₂ - (β₁ * β₁ + β₂ * β₂) * (c * c + d * d) := by
  simp [nuMat, Matrix.det_fin_two]
  ring

variable (Q : QData F K (unitaryInvolution K p f)) (c d : F)

@[expose] def nuOf (A : Su K p f 2) : Matrix (Fin 2) (Fin 2) F :=
  nuMat c d (Q.re (ent A 0 0)) (Q.im (ent A 0 0)) (Q.re (ent A 0 1)) (Q.im (ent A 0 1))

theorem det_nuOf (hcd : c * c + d * d = -1) (A : Su K p f 2) : (nuOf Q c d A).det = 1 := by
  rw [nuOf, det_nuMat, hcd]
  have := su_norm Q A
  linear_combination this

theorem nuOf_one : nuOf Q c d (1 : Su K p f 2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nuOf, nuMat, ent_one_zero_zero, ent_one_zero_one, Q.re_one, Q.im_one, Q.re_zero,
      Q.im_zero]

theorem nuMat_mul (hcd : c * c + d * d = -1) (a1 a2 b1 b2 A1 A2 B1 B2 : F) :
    nuMat c d (a1 * A1 - a2 * A2 - b1 * B1 - b2 * B2) (a1 * A2 + a2 * A1 + b1 * B2 - b2 * B1)
      (a1 * B1 - a2 * B2 + b1 * A1 + b2 * A2) (a1 * B2 + a2 * B1 - b1 * A2 + b2 * A1) =
    nuMat c d a1 a2 b1 b2 * nuMat c d A1 A2 B1 B2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nuMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-(B1 * b1 + B2 * b2)) * hcd
  · linear_combination (-(-B1 * b2 + B2 * b1)) * hcd
  · linear_combination (-(B1 * b2 - B2 * b1)) * hcd
  · linear_combination (-(B1 * b1 + B2 * b2)) * hcd

theorem nuOf_mul (hcd : c * c + d * d = -1) (A B : Su K p f 2) :
    nuOf Q c d (A * B) = nuOf Q c d A * nuOf Q c d B := by
  unfold nuOf
  rw [crd_mul_re_re Q, crd_mul_im_re Q, crd_mul_re_im Q, crd_mul_im_im Q]
  exact nuMat_mul c d hcd _ _ _ _ _ _ _ _

variable (hcd : c * c + d * d = -1)

@[expose] noncomputable def nuQ : Su K p f 2 →* SL(2, F) where
  toFun A := ⟨nuOf Q c d A, det_nuOf Q c d hcd A⟩
  map_one' := Subtype.ext (nuOf_one Q c d)
  map_mul' A B := Subtype.ext (nuOf_mul Q c d hcd A B)

theorem coe_nuQ (A : Su K p f 2) : ((nuQ Q c d hcd A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    nuOf Q c d A := rfl

end CFSG.ClassicalInvolution.PhanB3
