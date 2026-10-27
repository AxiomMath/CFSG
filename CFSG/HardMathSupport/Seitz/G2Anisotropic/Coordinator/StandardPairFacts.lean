module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Residuals
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.Quasithin.Background.G2URoots

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.G2U
  CFSG.LieType.Steinberg.Adjoint

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

theorem orderThreeSL_pow_three (K : Type) [Field K] : orderThreeSL K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orderThreeSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem orderThreeSL_ne_one (K : Type) [Field K] : orderThreeSL K ≠ 1 := by
  intro h
  have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [orderThreeSL] at this

theorem stronglyOrthogonal_12_10 :
    iform (τ := .G2) (vec 1 2) (vec 1 0) = 0 ∧ ¬ IsRoot .G2 (vec 1 2 + vec 1 0) ∧
      ¬ IsRoot .G2 (vec 1 2 - vec 1 0) := by
  refine ⟨by decide, fun h => ?_, fun h => ?_⟩
  · have := mem_rootList_of_isRoot h
    revert this
    decide
  · have := mem_rootList_of_isRoot h
    revert this
    decide

theorem coe_zStd (K : Type) [Field K] :
    ((zStd K : adjointGroup .G2 K) : ModGL .G2 K) = rootSL2 .G2 K ![1, 2] (orderThreeSL K) :=
  rfl

theorem coe_eStd (K : Type) [Field K] :
    ((eStd K : adjointGroup .G2 K) : ModGL .G2 K) = rootSL2 .G2 K ![1, 0] (orderThreeSL K) :=
  rfl

theorem zStd_pow_three (K : Type) [Field K] : zStd K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_zStd, ← map_pow, orderThreeSL_pow_three, map_one, Subgroup.coe_one]

theorem eStd_pow_three (K : Type) [Field K] : eStd K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_eStd, ← map_pow, orderThreeSL_pow_three, map_one, Subgroup.coe_one]

section Commute

theorem rootSL2_12_commute_10 (K : Type) [Field K] (A B : SL2 K) :
    rootSL2 .G2 K ![1, 2] A * rootSL2 .G2 K ![1, 0] B =
      rootSL2 .G2 K ![1, 0] B * rootSL2 .G2 K ![1, 2] A := by
  obtain ⟨h0, hp, hm⟩ := stronglyOrthogonal_12_10
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .G2 K isRoot_12 isRoot_10
    h0 hp hm _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

theorem zStd_mul_eStd (K : Type) [Field K] : zStd K * eStd K = eStd K * zStd K := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_zStd, coe_eStd]
  exact rootSL2_12_commute_10 K _ _

end Commute

end CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
