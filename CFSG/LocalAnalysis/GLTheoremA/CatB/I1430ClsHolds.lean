module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieDefs
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieThreeFork
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkAll
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430SporRows
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430SporBMA6B
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430SporBMA6M
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ONCover
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieRed
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoOutHolds
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

section LieThree


theorem i1430LieThree_holds : I1430LieThree :=
  i1430LieThree_of_fork H1420.lieOuterThree_holds

end LieThree

section Cls


theorem i1430Cls_holds
    : I1430Cls :=
  A6Spor.i1430Cls_of_BM_lie A6Spor.a6Row_B A6Spor.a6Row_M i1430ONCover_holds
      (i1430ClsLie_of_parts HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
          HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
          GLTheoremB.MovingAround.AltFacts4.inputAltNotLie_holds
          (kdChevDownQ_three_of_lieComp lieComp_holds) i1430LieThree_holds i1430LieTwoInn_holds
          i1430LieTwoOut_holds)

end Cls

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
