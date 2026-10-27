module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalSignedPerms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.CentralExt.QuaternionCover
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NormTail

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal OrthogonalTail CFSG.LieType.CentralExt
  CFSG.SectionRank.EvenCover

section Lifts

variable {K F : Type} [Field K] [Field F] [Algebra K F] (T : NormTailData K F) {r : ℕ}

theorem finite_of_finrank_eq_two [Finite K] (hF : Module.finrank K F = 2) : Finite F := by
  have : Module.Finite K F := Module.finite_of_finrank_pos (by omega)
  exact Module.finite_of_finite K

theorem swapSL_mul_diagSL (s : Fˣ) : swapSL F * diagSL F s = diagSL F s⁻¹ * swapSL F := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  change ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)]) a b =
    ((!![((s⁻¹ : Fˣ) : F), 0; 0, ((s⁻¹⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) *
      !![(0 : F), 1; -1, 0]) a b
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  fin_cases a <;> fin_cases b <;> simp

theorem barSL_diagSL (s : Fˣ) :
    barSL T (diagSL F s) = diagSL F (Units.map (T.bar : F →* F) s) := by
  ext a b
  rw [coe_barSL, coe_diagSL, coe_diagSL]
  fin_cases a <;> fin_cases b <;> simp [Units.coe_map]

variable [CharP K 2] {E : Type*} [Group E] (π : E →* G0 T r)

variable [Finite K] [Finite E] {T π}

end Lifts

end CFSG.LocalAnalysis.ComponentInitial.NormTail
