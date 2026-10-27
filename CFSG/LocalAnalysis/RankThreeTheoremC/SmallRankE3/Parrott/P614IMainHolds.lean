module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IKFact
public import CFSG.Milestones.ASVolI.C135.WMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IC134Weak

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

section Holds

set_option linter.unusedSectionVars false


theorem kFactCampbellBlock_holds
    : KFactCampbellBlock :=
  kFactCampbellBlock_of_asC134Weak CFSG.Quasithin.MS93.burnsideC134w_corrOneWeak

theorem piece620iii_holds
    : Piece620iii :=
  piece620iii_of_kFactCampbellBlock kFactCampbellBlock_holds

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
