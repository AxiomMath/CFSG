module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix

variable (F : Type) [Field F]

@[expose] def gram7 : Matrix (Fin 7) (Fin 7) F :=
  Matrix.of fun i j =>
    if ((i : ℕ) < 3 ∧ (j : ℕ) = i + 3) ∨ ((j : ℕ) < 3 ∧ (i : ℕ) = j + 3) ∨
      ((i : ℕ) = 6 ∧ (j : ℕ) = 6) then 1 else 0

theorem transpose_gram7 : (gram7 F)ᵀ = gram7 F := by
  ext i j
  simp only [transpose_apply, gram7, of_apply]
  congr 1
  apply propext
  omega

theorem gram7_mul_self : gram7 F * gram7 F = 1 := by
  ext i j
  rw [mul_apply, Fin.sum_univ_seven]
  fin_cases i <;> fin_cases j <;> simp [gram7, one_apply]

theorem transpose_blockSwapJ_six :
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 : Matrix (Fin 6) (Fin 6) F)ᵀ =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 := by
  ext i j
  simp only [transpose_apply, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ,
    of_apply]
  congr 1
  apply propext
  omega

theorem blockSwapJ_six_mul_self :
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 : Matrix (Fin 6) (Fin 6) F) *
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 = 1 := by
  ext i j
  rw [mul_apply, Fin.sum_univ_six]
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ, one_apply]

@[expose] def graphGram6 : GL (Fin 6) F :=
  ⟨CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3,
    blockSwapJ_six_mul_self F, blockSwapJ_six_mul_self F⟩

@[expose] def graphGram7 : GL (Fin 7) F :=
  ⟨gram7 F, gram7 F, gram7_mul_self F, gram7_mul_self F⟩

@[simp] theorem coe_graphGram6 :
    ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 :=
  rfl

@[simp] theorem coe_graphGram7 :
    ((graphGram7 F : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) = gram7 F :=
  rfl

@[simp] theorem coe_graphGram6_inv :
    (((graphGram6 F)⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 :=
  rfl

@[simp] theorem coe_graphGram7_inv :
    (((graphGram7 F)⁻¹ : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) = gram7 F :=
  rfl

theorem graphGram6_inv : (graphGram6 F)⁻¹ = graphGram6 F :=
  Units.ext rfl

theorem graphGram7_inv : (graphGram7 F)⁻¹ = graphGram7 F :=
  Units.ext rfl

end CFSG.SeitzReduction.F4Pilot
