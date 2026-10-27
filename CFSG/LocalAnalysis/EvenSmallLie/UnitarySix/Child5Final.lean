module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Assembly
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3EInput

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaSec3

section L


theorem sec3LInput : Sec3LInput := by
  intro G _ _ L _ _ _ t e
  exact ⟨fun X hXS hcomm hX => sS_abelian_eq_sA₂ e X hXS hcomm hX, normalizer_sA₂_le e,
    centralizer_z_le e⟩

end L

section Main

theorem childU6Centerless_of_open (hA : HypAutInput) (hcase : CaseInput)
    (hY : Y13CoordInput) (hY₂ : Y14CoordInput) (hP₁ : N1PInput) : ChildU6Centerless :=
  childU6Centerless_of_inputs hA hcase sec3LInput hY hY₂ hP₁

end Main

end CFSG.EvenSmallLie.UnitarySix.Child5
