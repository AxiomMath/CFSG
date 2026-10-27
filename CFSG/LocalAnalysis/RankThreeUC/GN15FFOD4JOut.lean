module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Holds
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFONoOffender
public import CFSG.LocalAnalysis.RankThreeUC.GN15HoldsFF

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

set_option linter.unusedSectionVars false

theorem ffOffenderInvertsOdd_of_noOffender_holds
    (hvacL : FFO.PSLNoOffender)
    (hvacU : FFO.PSUNoOffender) : FFOffenderInvertsOdd :=
  ffOffenderInvertsOdd_of_noOffender hvacL hvacU ffOffenderInvertsOddD4_holds

theorem jOutCentral_of_noOffender_holds
    (hvacL : FFO.PSLNoOffender)
    (hvacU : FFO.PSUNoOffender) : JOutCentral :=
  jOutCentral_of_ffOffender_holds (ffOffenderInvertsOdd_of_noOffender_holds hvacL hvacU)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
