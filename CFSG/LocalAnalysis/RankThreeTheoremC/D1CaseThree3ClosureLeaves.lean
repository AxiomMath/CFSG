module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Closure
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Leaves3
import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeK

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

theorem D1CaseThreeG28A15Facts.of_leaves (hL : D2KFactLeaves) (hSchur : KFactChevTwoSurvivorSchur)
    (hG28 : KFactG28Local) (hA15 : KFactA15Local) (hOut : KFactBlockThreeOut)
    (hSU : KFactBlockNoSU38) (hFive : KFactBlockFiveNoncyclic) (hFives : KFactBlockThreeFives) :
    D1CaseThreeG28A15Facts where
  eightFour := hL.eightFour
  eightFive := hL.eightFive
  eightSix := hL.eightSix
  nineThree := hL.nineThree
  noXBlock := d1NoXBlock_of_inputsK hL.aschbacherOne hL.aschbacherTwo hL.solomonAlt
  parabolicThree := hL.parabolicThree
  citedBlockThree := hL.citedBlockThree
  blockThreeAltSeven := hL.blockThreeAltSeven
  threeOrFiveDvd := hL.threeOrFiveDvd
  catalogOuterSolvable := fun S _ _ _ hnab hcat => hL.catalogSchreier S ‹_› hnab hcat
  survivorSchur := hSchur
  g28Local := hG28
  a15Local := hA15
  blockThreeOut := hOut
  blockNoSU38 := hSU
  blockFiveNoncyclic := hFive
  blockThreeFives := hFives

end CFSG.LocalAnalysis.RankThreeTheoremC
