module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Leaves3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

structure D2KFactLeavesCoreF : Prop where
  seitzRankTwo : KFactSeitzRankTwo
  nineThree : Asc81bNineThree
  aschbacherTwo : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK
  solomonAlt : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK

theorem D2KFactLeavesCoreF.toCore (h : D2KFactLeavesCoreF)
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (h3 : CitedBlockThreeTransvection)
    (hA7 : KFactBlockThreeAltSeven) (hPP : KFactParabolicPrime)
    (h3p : CitedBlockTransvectionPrime) (hA7p : KFactBlockAltSevenPrime)
    (hSec : KFactBlockAltFiveSectionInner) (hSq : KFactBlockAltFiveSquareInner) :
    D2KFactLeavesCore :=
  ⟨h.seitzRankTwo, h.nineThree, h3, hA7, hPP, h3p, hA7p, h1, h.aschbacherTwo, h.solomonAlt,
    hSec, hSq, hJ4⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
