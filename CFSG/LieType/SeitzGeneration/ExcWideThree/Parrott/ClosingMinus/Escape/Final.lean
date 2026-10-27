module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.Plane
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.NF
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.TwoLine

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape

open CFSG.LieType.SeitzGeneration.ExcWideThree

section Final

theorem trialityThreePlanesOdd_holds : TrialityThreePlanesOdd :=
  trialityThreePlanesOdd_of_inputs twoLineGen_holds outerToralForm_holds

end Final

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape
