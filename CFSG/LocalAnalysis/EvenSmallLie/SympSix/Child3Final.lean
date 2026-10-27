module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Inputs
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.EvenSmallLie.Child3

theorem childSp6Centerless_of_gaps (hG1 : GapEpsilonOne) (hG2 : GapLagrangianSelector)
    (hG3 : GapAltEight) : ChildSp6Centerless :=
  childSp6Centerless_of_schreier_of_gaps CFSG.RankThree.PartOne.SPOR.schreierFor_catalog hG1 hG2
    hG3

end CFSG.EvenSmallLie.Child3
