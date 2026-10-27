module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.SlotFrontier

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem slotP614CaseDelta_of_pieces (hCD : PieceCaseDelta) (k292 : KFact292)
    (kT29 : KFactProofs.T29.GL83I291Three) (kNC : KFactProofs.T29.NoncyclicCentreRank)
    (kQ : KFactThreeComponentsQRank) : SlotP614CaseDelta :=
  hCD k292 kT29 kNC kQ

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
