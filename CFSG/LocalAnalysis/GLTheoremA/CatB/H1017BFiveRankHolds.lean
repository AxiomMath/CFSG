module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFiveTwoD
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFive
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFivePure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017


theorem twoRankLe_five_B
    : TwoRankLe 5 .B 2 :=
  twoRankLe_five_B_of_fiveBPure (babyFiveBPureFact_of_twoDFiveA babyTwoDFiveAFact_holds)

end CFSG.LocalAnalysis.GLTheoremA.H1017
