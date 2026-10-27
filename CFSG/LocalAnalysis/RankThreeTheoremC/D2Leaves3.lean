module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2TheoremZ3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L2MSide3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2AltFive3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporOpen3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PrimeThree3Leaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PrimeThree3Seitz
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

structure D2KFactLeavesCore : Prop where
  seitzRankTwo : KFactSeitzRankTwo
  nineThree : Asc81bNineThree
  citedBlockThree : CitedBlockThreeTransvection
  blockThreeAltSeven : KFactBlockThreeAltSeven
  parabolicPrime : KFactParabolicPrime
  citedBlockPrime : CitedBlockTransvectionPrime
  blockAltSevenPrime : KFactBlockAltSevenPrime
  aschbacherOne : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK
  aschbacherTwo : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK
  solomonAlt : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK
  blockAltFiveSection : KFactBlockAltFiveSectionInner
  blockAltFiveSquare : KFactBlockAltFiveSquareInner
  heisLocalJ4Eleven : D2HeisLocalAt (.sporadic .J4) fun p => p = 11

structure D2KFactLeaves : Prop extends D2KFactLeavesCore where
  localCGT : AschbacherLocalCGTBlock
  eightFour : Asc81bEightFour
  eightFive : Asc81bEightFive
  eightSix : Asc81bEightSix
  parabolicThree : KFactParabolicThree
  twoGenInner : KFactTwoGenInner
  lieCharRank : KFactLieCharRank
  catalogSchreier : KFactCatalogSchreier
  seitzRankThree : KFactSeitzRankThreeExceptions
  sections : SporSectionFacts3
  threeOrFiveDvd : KFactThreeOrFiveDvd
  sporVacuous : D2SporadicVacuous3

structure D2Leaves3 (G : Type) [Group G] [Finite G] : Prop where
  u3Three : D2U3ThreeStrong3 G
  seitzExc : D2SeitzExcRestStrong3 G
  altFive : D2AltFive3 G
  altSix : D2AltSixStrong3 G
  spor : D2SporadicOpen3 G

theorem D2KFactLeaves.noXBlock3 (hK : D2KFactLeaves) : D1NoXBlock3 G :=
  d1NoXBlock3_of_inputsK hK.aschbacherOne hK.aschbacherTwo hK.solomonAlt

theorem D2KFactLeaves.theoremZ3 (hK : D2KFactLeaves) : D2TheoremZ3 G :=
  d2TheoremZ3_of hK.noXBlock3 hK.eightFour hK.localCGT

theorem D2KFactLeaves.l2MSide3 (hK : D2KFactLeaves) : D2L2MSide3 G :=
  d2L2MSide3_of hK.noXBlock3 hK.threeOrFiveDvd hK.catalogSchreier hK.eightFour hK.eightFive
    hK.eightSix hK.nineThree hK.parabolicThree hK.citedBlockThree hK.blockThreeAltSeven
    hK.twoGenInner hK.parabolicPrime hK.citedBlockPrime hK.blockAltSevenPrime

theorem D2Leaves3.seitzExc3 (hK : D2KFactLeaves) (h : D2Leaves3 G) : D2SeitzExc3 G :=
  d2SeitzExc3_of_rest3 hK.seitzRankThree
    (d2SeitzExcRest3_of_strong hK.eightFour hK.noXBlock3 h.seitzExc)

theorem D2Leaves3.sporadicCase3 (hK : D2KFactLeaves) (h : D2Leaves3 G) : D2SporadicCase3 G :=
  d2SporadicCase3_of_rest3 hK.sections (d2SporadicRest3_of_open3 hK.sporVacuous h.spor)

theorem D2Leaves3.u3Three3 (hK : D2KFactLeaves) (h : D2Leaves3 G) : D2U3Three3 G :=
  d2U3Three3_of_strong hK.eightFour hK.noXBlock3 h.u3Three

theorem D2Leaves3.altSixCase3 (hK : D2KFactLeaves) (h : D2Leaves3 G) : D2AltSixCase3 G :=
  d2AltSixCase3_of_strong hK.eightFour hK.noXBlock3 h.altSix

theorem D2Leaves3.caseU33 (hK : D2KFactLeaves) (h : D2Leaves3 G) : D2CaseU33 G :=
  d2CaseU33_of hK.lieCharRank hK.seitzRankTwo (h.seitzExc3 hK) (h.sporadicCase3 hK)
    (h.u3Three3 hK) hK.noXBlock3 hK.threeOrFiveDvd hK.catalogSchreier hK.eightFour hK.eightFive
    hK.eightSix hK.nineThree hK.parabolicThree hK.citedBlockThree hK.blockThreeAltSeven
    hK.twoGenInner hK.parabolicPrime hK.citedBlockPrime hK.blockAltSevenPrime hK.localCGT

theorem D2Leaves3.componentCaseMax3 (hK : D2KFactLeaves) (h : D2Leaves3 G) :
    D2ComponentCaseMax3 G :=
  d2ComponentCaseMax3_of_current3 hK.lieCharRank hK.seitzRankTwo hK.theoremZ3 hK.l2MSide3
    (h.caseU33 hK) (h.seitzExc3 hK) (d2AltNoConfig3_of_five3 h.altFive) (h.altSixCase3 hK)
    (h.sporadicCase3 hK)

end CFSG.LocalAnalysis.RankThreeTheoremC
