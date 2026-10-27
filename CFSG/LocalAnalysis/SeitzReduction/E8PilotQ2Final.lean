module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PieceMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2FieldAssembly
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalThree

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

namespace E8Pilot

theorem e8TwoFieldRowInput_holds : E8TwoFieldRowInput :=
  e8TwoFieldRowInput_of_pieceInput e8TwoFieldPieceInput_holds

end E8Pilot

section Family

theorem seitzExclusion_highE8_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    SeitzExclusion (HighExceptional .E8) :=
  seitzExclusion_highE8_of_final3 hGLS E8Pilot.e8TwoFieldRowInput_holds

end Family

end CFSG.SeitzReduction
