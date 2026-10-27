module

public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutOdd
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FFGlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

set_option linter.unusedSectionVars false

theorem jOutCentral_of_ffOffender_holds
    (hS : FFOffenderInvertsOdd) : JOutCentral :=
  jOutCentral_of_ffOffender CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds hS

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

end
