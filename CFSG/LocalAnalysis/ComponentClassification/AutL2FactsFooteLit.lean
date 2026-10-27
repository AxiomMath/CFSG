module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL2Facts
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsNineOddInner
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteRank
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteSolv

public section

namespace CFSG.ComponentClassification.AutL2Facts

theorem cfFooteL2OutAbelian : FooteLit.FooteL2OutAbelian := footeOutAbelian

theorem cfFooteL2AbelianCore : FooteLit.FooteL2AbelianCore := footeAbelianCore

theorem cfFooteL2NineOddInner : FooteLit.FooteL2NineOddInner := footeNineOddInner

theorem cfFooteL2InvolutionSolvable : FooteLit.FooteL2InvolutionSolvable :=
  footeInvolutionSolvable

theorem cfFooteL2RankThree : FooteLit.FooteL2RankThree := footeRankThree

end CFSG.ComponentClassification.AutL2Facts
