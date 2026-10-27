module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_quadMinus_of_finite)

noncomputable abbrev fa8Q0 : QuadraticForm (ZMod 3) (Fin (2 * 4) → ZMod 3) :=
  coordinateQuadMinus 4 (ZMod 3) (by norm_num) 0 1

private theorem fa8_irreducible : ∀ s : ZMod 3, s ^ 2 + 0 * s + 1 ≠ 0 := by decide

theorem fa8_std_nondegenerate : fa8Q0.Nondegenerate :=
  (coordinateMinusIsometry 4 (ZMod 3) (by norm_num) 0 1).nondegenerate_iff.mp
    (nondegenerate_quadMinus_of_finite 4 (ZMod 3) fa8_irreducible)

theorem fa8_std_finrank : Module.finrank (ZMod 3) (Fin (2 * 4) → ZMod 3) = 8 := by
  rw [Module.finrank_fin_fun]

theorem fa8_std_quadSign : quadSign fa8Q0 = -1 := by
  have h := quadSign_congr (nondegenerate_quadMinus_of_finite 4 (ZMod 3) fa8_irreducible)
    ⟨coordinateMinusIsometry 4 (ZMod 3) (by norm_num) 0 1⟩
  exact h.symm.trans (quadSign_quadMinus (m := 4) (by norm_num) fa8_irreducible)

end CFSG.OddStandard.SmallF3.Omega
