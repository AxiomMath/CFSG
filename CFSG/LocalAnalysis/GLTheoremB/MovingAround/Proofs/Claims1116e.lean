module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129W
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116e

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex Bal207Index IsL2EightIndex
  Gen2318Index Bal209TwoIndex IsTwistedE6FourIndex IsSixIndex IsF4EightIndex IsD4FourIndex FourIndex
  IsTwoPow Seitz2310CubeSimple)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo)
open GL83.CompFam

set_option linter.unusedSectionVars false

theorem characteristic_eq_two_of_excIndex_three {d : TauCeti.LieTypeIndex} (h : ExcIndex 3 d) :
    d.characteristic = 2 := by
  by_contra hc
  cases d <;> simp_all [ExcIndex, Bal207Index, IsL2EightIndex, Gen2318Index, Bal209TwoIndex,
    IsTwistedE6FourIndex, IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex, IsTwoPow]

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116e

end
