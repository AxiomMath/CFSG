module

public import CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup

public section

namespace CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData

open scoped MatrixGroups
open CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup

@[expose] noncomputable def upperPSL (F : Type) [Field F] : Multiplicative F →* PSL(2, F) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, F))).comp (upper F)

@[expose] noncomputable def upperSubgroup (F : Type) [Field F] : Subgroup PSL(2, F) :=
  (upperPSL F).range

@[expose] noncomputable def diagonalSL (F : Type) [Field F] : Fˣ →* SL(2, F) where
  toFun a := ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    show (!![((a * b : Fˣ) : F), 0; 0, (((a * b)⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) =
      !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] * !![(b : F), 0; 0, ((b⁻¹ : Fˣ) : F)]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[expose] noncomputable def diagonalPSL (F : Type) [Field F] : Fˣ →* PSL(2, F) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, F))).comp (diagonalSL F)

@[expose] noncomputable def torus (F : Type) [Field F] : Subgroup PSL(2, F) :=
  (diagonalPSL F).range

variable {F : Type} [Field F]

theorem upperPSL_apply (a : Multiplicative F) :
    upperPSL F a = QuotientGroup.mk (upper F a) := rfl

theorem diagonalPSL_apply (a : Fˣ) :
    diagonalPSL F a = QuotientGroup.mk (diagonalSL F a) := rfl

theorem upperPSL_injective : Function.Injective (upperPSL F) := psl_upper_injective

theorem upperPSL_mem (a : Multiplicative F) : upperPSL F a ∈ upperSubgroup F := ⟨a, rfl⟩

theorem diagonalPSL_mem (a : Fˣ) : diagonalPSL F a ∈ torus F := ⟨a, rfl⟩

theorem diagonalSL_apply_zero_zero (a : Fˣ) :
    ((diagonalSL F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = a := rfl

theorem diagonalSL_apply_one_one (a : Fˣ) :
    ((diagonalSL F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = ((a⁻¹ : Fˣ) : F) := rfl

theorem diagonalSL_apply_zero_one (a : Fˣ) :
    ((diagonalSL F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := rfl

theorem diagonalSL_apply_one_zero (a : Fˣ) :
    ((diagonalSL F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl

theorem upper_apply_zero_zero (a : Multiplicative F) :
    ((upper F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := rfl

theorem upper_apply_one_zero (a : Multiplicative F) :
    ((upper F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl

theorem upper_apply_one_one (a : Multiplicative F) :
    ((upper F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := rfl

theorem upperSubgroup_card_of_finite [Finite F] :
    Nat.card (upperSubgroup F) = Nat.card F := by
  unfold upperSubgroup
  rw [← Nat.card_congr (MonoidHom.ofInjective (upperPSL_injective (F := F))).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

end CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData
