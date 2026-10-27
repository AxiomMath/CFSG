module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOHolds
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOLinkPSL
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOLinkPSU

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

theorem ffOffenderInvertsOdd_of_noOffender
    (hvacL : FFO.PSLNoOffender) (hvacU : FFO.PSUNoOffender)
    (hD4 : FFOffenderInvertsOddD4) : FFOffenderInvertsOdd :=
  ffOffenderInvertsOdd_holds_of_families (FFO.ffOffenderInvertsOddPSL_of_noOffender hvacL)
    (FFO.ffOffenderInvertsOddPSU_of_noOffender hvacU) hD4

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

end
