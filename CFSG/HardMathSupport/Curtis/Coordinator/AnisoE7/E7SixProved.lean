module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.Final
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.LinesA5

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

set_option linter.unusedSectionVars false


theorem e7SixStep3Adj_proved : E7SixStep3Adj := e7SixStep3Adj_of_A5 e7SixLinesKind_3

theorem excCubeHighAt_E7_six_proved :
    CFSG.HardMathSupport.Malle.SeitzCube.ExcCubeHighAt TauCeti.LieTypeIndex.E7 6 :=
  excCubeHighAt_E7_six_of_A5 e7SixLinesKind_3

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
