module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedLeviModelRigidMain
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalFive

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section Reduction

theorem twistedE6GraphRowDInput_of_piModel (hY : TwistedLeviPiModelInput) :
    TwistedE6GraphRowDInput :=
  twistedE6GraphRowDInput_of_inputs twistedA3MatrixRigidityInput_holds hY

end Reduction

section Main

theorem seitzExclusion_highF4_of_piModel (hGLS : GLS3OddLieAutComponentsInput)
    (hY : TwistedLeviPiModelInput) (h2 : TwoRowsInput) :
    SeitzExclusion (HighExceptional .F4) :=
  CFSG.SeitzReduction.seitzExclusion_highF4_of_final5 hGLS
    (twistedE6GraphRowDInput_of_piModel hY) h2

end Main

end CFSG.SeitzReduction.F4Pilot
