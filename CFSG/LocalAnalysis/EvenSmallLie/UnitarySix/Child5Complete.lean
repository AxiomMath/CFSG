module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Done
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Y14Pack
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3K1Model

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

section K1


theorem k1ModelInput : K1ModelInput := by
  intro G _ _ L _ _ _ t _ _ e
  exact YamadaSec3.exists_k1Model e t

end K1

section Main

theorem childU6Centerless_of_hypAut (hA : HypAutInput) (hcase : CaseInput) : ChildU6Centerless :=
  childU6Centerless_of_done' hA hcase YamadaSec3.y14CoordInput k1ModelInput

end Main

end CFSG.EvenSmallLie.UnitarySix.Child5
