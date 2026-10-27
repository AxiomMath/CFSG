module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.CaseOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.CaseTwo
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalA
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalB
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Embed
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCover
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Lemma38
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.ProperTwoGeneratedCore.Assembly

theorem theoremC :
    TheoremCStatement :=
  theoremC_of_parts caseTwoReduction
    (highRankStrongEmbedding CFSG.ShultStronglyClosedTI.theoremTwo
      (quotientLocalEmbedding caseOneInvolutions quasiRankThree))
    (benderCoverExclusion benderBorelFactsHold)

theorem highRankEscapingStep :
    HighRankEscapingStep :=
  highRankEscapingStep_of_theoremC theoremC

end CFSG.ProperTwoGeneratedCore.TheoremC
