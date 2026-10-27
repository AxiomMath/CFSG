module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Lang.TwE6Step3.PlaneConj
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartOne.KE6.E8T3Stab
public import CFSG.RankThree.PartOne.KE6.Tw6Transport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

variable {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L}

@[expose] def tw6SixLayerRoots (w : WeylGroup Tag.E6) (i : Fin 2) : Set (Fin Tag.E6.rank → ℤ) :=
  (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6
    (![CFSG.RankThree.E6.support13, CFSG.RankThree.E6.support56] i)

@[expose] def tw6SixLayer (w : WeylGroup Tag.E6) (i : Fin 2) : Subgroup (ModGL Tag.E6 L) :=
  rootSpan Tag.E6 L (tw6SixLayerRoots w i) ⊓ twistedFixedPoints (tw6N L) (twistE6 L Fr)

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
