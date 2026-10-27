module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOFamilies
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FFGlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

set_option linter.unusedSectionVars false

theorem ffOffenderInvertsOdd_holds_of_families
    (hPSL : FFOffenderInvertsOddPSL)
    (hPSU : FFOffenderInvertsOddPSU) (hD4 : FFOffenderInvertsOddD4) : FFOffenderInvertsOdd :=
  ffOffenderInvertsOdd_of_families
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds hPSL hPSU hD4

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

end
