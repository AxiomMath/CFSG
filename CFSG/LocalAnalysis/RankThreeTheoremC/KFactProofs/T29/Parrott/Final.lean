module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankOne
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Fusion

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

section CentRank


theorem centRankOpen_of_fusion (h2a : OuterFixedE9) (h2b : InnerFusionE9Exc) : CentRankOpen :=
  centRankOpen_of_kfacts h2a (innerFusionE9_of_exc h2a h2b) rankFourOpen_holds rankOneAut_holds

end CentRank

section Main


theorem t29ChevOther_of_kfacts (hL3 : T29LThreeEpsCase) (h2a : OuterFixedE9)
    (h2b : InnerFusionE9Exc) : T29ChevOther :=
  t29ChevOther_of_inputs hL3 (centRankOpen_of_fusion h2a h2b)

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
