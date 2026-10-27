module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Closure
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs
public import CFSG.RankThree.PartTwo.Sec21.Item234
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeReeF4
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48DataDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

structure D1CaseThreeFineKFacts3 : Prop extends D1CaseThreeG28A15Facts where
  beta : KFactBetaRank2
  p1Lie : KFactP1ThreeLie
  p1Alt : KFactP1ThreeAlt
  p1Spor : KFactP1ThreeSpor
  localCGT : AschbacherLocalCGTBlock
  reeF4Local : KFactReeF4Local
  reeF4Target : StmtReeF4Target
  jStarElimReeF4 : KFactJStarElimReeF4
  blockFiveParabolic : KFactBlockFiveParabolic
  outFiveCyclic : KFactOutFiveCyclic
  j3Sylow : KFactJ3Sylow
  j3OuterInvolution : KFactJ3OuterInvolution
  j3OuterRank : KFactJ3OuterRank
  j3Target : StmtJ3Target
  j3TargetCard : StmtJ3TargetCard
  jStarElimJ3 : KFactJStarElimJ3
  blockThreeSolvable : KFactBlockThreeSolvable
  jStarElimLie : KFactJStarElimLie
  jStarElimAlt : KFactJStarElimAlt
  jStarElimSpor : KFactJStarElimSpor
  lemmaB : StmtLemmaB
  outElemRank : KFactOutElemRank
  sp48Local : KFactSp48Local
  sp48Data : KFactSp48Data
  sp48NonsolvLocal : KFactSp48NonsolvLocal
  sp48Target : StmtSp48Target
  jStarElimSp48 : KFactJStarElimSp48
  blockThreeOrderNine : KFactBlockThreeOrderNine
  blockL28Transvection : KFactBlockL28Transvection
  blockL28Rank : KFactBlockL28Rank
  blockL28TwoRank : KFactBlockL28TwoRank
  sp62Local : KFactSp62Local
  blockLeviU42 : KFactBlockLeviU42
  omegaEightMinusAut : KFactOmegaEightMinusAut
  u62ThreeRank : KFactU62ThreeRank
  omegaMinusThreeRank : KFactOmegaMinusThreeRank
  gl83 : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable
  sp62Frame : KFactSp62Frame
  omega8Frame : KFactOmega8Frame
  a9Local : KFactA9Local
  jStarElimA3p : KFactJStarElimA3p 3 (3 ^ 4)
  blockThreeOneOrbit : KFactBlockThreeOneOrbit

end CFSG.LocalAnalysis.RankThreeTheoremC
