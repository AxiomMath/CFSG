module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearUnitaryFamily
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SymplecticOrthogonalFamily

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

theorem lieComp_of_classical
    (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3)
    (hD4 : D4OuterExport) (hExc : LieCompOn .exceptional) (hSRT : LieCompOn .suzukiReeTits) :
    LieComp :=
  lieComp_of_families fun F => by
    cases F
    · exact lieCompOn_linearUnitary hb hQ
    · exact lieCompOn_symplecticOrthogonal hb hQ hD4
    · exact hExc
    · exact hSRT

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
