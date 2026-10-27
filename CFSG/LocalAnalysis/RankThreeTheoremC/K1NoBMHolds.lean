module

public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMSeitz
public import CFSG.LieType.SeitzGeneration.InnerExHolds
import CFSG.LieType.SeitzGeneration.ConsumerEx
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentCharPSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporHS5

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Blueprint CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC (NotBM StronglyEmbeddedRankTwoKFactNoBM)

section SeitzEx


theorem stronglyEmbeddedRankTwoKFactNoBM_of_seitzEx
    (hS : CFSG.LieType.SeitzGeneration.KFactSeitzRankTwoInnerEx) :
    StronglyEmbeddedRankTwoKFactNoBM :=
  stronglyEmbeddedRankTwoKFactNoBM_of_smallIdent
    (kFactSmallIdentNoBM_of_families smallIdentAlt smallIdentLieCharP
      (smallIdentLieOffChar_of_gen (CFSG.LieType.SeitzGeneration.offCharGen_of_seitzEx hS))
      fun s hsB hsM =>
        smallIdentSporAt_of_rows_noB sporProvedRows sporFi24SevenRow
          CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group card_carrier_eq_d2SporadicOrder
          s hsM hsB sporGammaOneAt_HS_five)

end SeitzEx

section Holds


theorem stronglyEmbeddedRankTwoKFactNoBM_holds : StronglyEmbeddedRankTwoKFactNoBM :=
  stronglyEmbeddedRankTwoKFactNoBM_of_seitzEx
    CFSG.LieType.SeitzGeneration.kFactSeitzRankTwoInnerEx_holds

end Holds

end CFSG.AGLEmbedding
