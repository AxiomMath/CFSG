module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.PlaneMain
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.Lines01
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.RSub

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

set_option linter.unusedSectionVars false


theorem e7SixStep3Adj_of_A5 (h3 : E7SixLinesKind [3]) : E7SixStep3Adj :=
  e7SixStep3Adj_of_kinds h3 e7SixLinesKind_01 e7SixRSub

theorem excCubeHighAt_E7_six_of_A5 (h3 : E7SixLinesKind [3]) :
    CFSG.HardMathSupport.Malle.SeitzCube.ExcCubeHighAt TauCeti.LieTypeIndex.E7 6 :=
  CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.excCubeHighAt_E7_six_of_plane
    (e7SixPlane_of_step3Adj (e7SixStep3Adj_of_A5 h3))

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
