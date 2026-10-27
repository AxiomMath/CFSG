module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3G28
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3A15

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

structure D1CaseThreeG28A15Facts : Prop where
  eightFour : Asc81bEightFour
  eightFive : Asc81bEightFive
  eightSix : Asc81bEightSix
  nineThree : Asc81bNineThree
  noXBlock : D1NoXBlock
  parabolicThree : KFactParabolicThree
  citedBlockThree : CitedBlockThreeTransvection
  blockThreeAltSeven : KFactBlockThreeAltSeven
  threeOrFiveDvd : KFactThreeOrFiveDvd
  catalogOuterSolvable : CatalogOuterSolvable
  survivorSchur : KFactChevTwoSurvivorSchur
  g28Local : KFactG28Local
  a15Local : KFactA15Local
  blockThreeOut : KFactBlockThreeOut
  blockNoSU38 : KFactBlockNoSU38
  blockFiveNoncyclic : KFactBlockFiveNoncyclic
  blockThreeFives : KFactBlockThreeFives

variable {G : Type} [Group G] [Finite G]

theorem D1CaseThreeG28A15Facts.g28 (h : D1CaseThreeG28A15Facts) :
    D1CaseThreeLieAt3 G fun p d =>
      p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .G2 q :=
  d1CaseThreeG28At3_closed h.survivorSchur h.g28Local h.eightFour h.eightFive h.eightSix
    h.nineThree h.noXBlock h.parabolicThree h.citedBlockThree h.blockThreeAltSeven
    h.blockThreeOut h.blockNoSU38

theorem D1CaseThreeG28A15Facts.a15 (h : D1CaseThreeG28A15Facts) :
    D1CaseThreeA3pAt3 G (· = 5) :=
  d1CaseThreeA15At3_closed h.a15Local h.eightFour h.eightFive h.eightSix h.nineThree h.noXBlock
    h.parabolicThree h.citedBlockThree h.blockThreeAltSeven h.threeOrFiveDvd
    h.catalogOuterSolvable h.blockFiveNoncyclic h.blockThreeFives

end CFSG.LocalAnalysis.RankThreeTheoremC
