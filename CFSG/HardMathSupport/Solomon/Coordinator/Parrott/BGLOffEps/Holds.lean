module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16Main
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16FieldMain
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUTHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Char3Main
public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Char3Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps

section Holds


theorem bglFieldGenerationWithXOffEps_holds : BGLFieldGenerationWithXOffEps :=
  bglFieldGenerationWithXOffEps_of_halves bglOffEpsCharThree_holds bglOffEpsU38_holds

theorem input23_16Three_holds : Input23_16Three :=
  input23_16Three_of_withX
      (bglFieldGenerationWithXThree_of_pair bglFieldPairGeneration_holds
          bglFieldGenerationWithXOffEps_holds) field3Structure_holds

end Holds

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps
