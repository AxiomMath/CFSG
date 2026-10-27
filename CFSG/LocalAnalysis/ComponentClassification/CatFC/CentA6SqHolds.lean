module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqEven
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClShapes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC


theorem a6OddArm_holds : A6OddArm :=
  a6OddArm_of_shapes armInputs_holds.order
    (oddA6Shape_of_inputs armInputs_holds.order armInputs_holds.gls)

theorem kgA6Sq_holds : EvenSporadicStandard.HSStd.Zassenhaus.PartA.KGA6Sq :=
  kgA6Sq_of_arms armInputs_holds a6OddArm_holds (a6EvenArm_of_order armInputs_holds.order)

end CFSG.ComponentClassification.CatFC
