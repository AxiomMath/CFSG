module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Final
import CFSG.LocalAnalysis.GLTheoremA.CatB.No5Lie
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420


theorem i1420M3A_proved : I1420M3A :=
  i1420M3A_holds CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    (fun q => CFSG.LocalAnalysis.GLTheoremA.kdChevDownQ_three_of_lieComp
      CFSG.LocalAnalysis.GLTheoremA.lieComp_holds q)
    (fun q => CFSG.LocalAnalysis.GLTheoremA.No5.kdChevDownQ_five q)
    CFSG.LocalAnalysis.GLTheoremA.kdAltDown_holds

theorem i1420M5A_proved : I1420M5A :=
  i1420M5A_holds CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    (fun q => CFSG.LocalAnalysis.GLTheoremA.kdChevDownQ_three_of_lieComp
      CFSG.LocalAnalysis.GLTheoremA.lieComp_holds q)
    (fun q => CFSG.LocalAnalysis.GLTheoremA.No5.kdChevDownQ_five q)
    CFSG.LocalAnalysis.GLTheoremA.kdAltDown_holds

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
