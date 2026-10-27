module

public import CFSG.Assembly.E6FourNeighbourFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListLieModels
import CFSG.LocalAnalysis.StandardType.Marking
import all CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges
public import CFSG.Assembly.StandardTypeRecognitionDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.Quasithin.EmptyFaithful.S146zYFacts
import CFSG.Quasithin.EmptyFaithful.S146zYRes
import CFSG.Quasithin.H13.NQCoreP134Main
import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs

public section

namespace CFSG.Assembly

open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.StandardType
  CFSG.Assembly.LowTwoRank TauCeti
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (lieModel_typeA lieModel_lie
  lieModel_of_classical)

theorem e6Four_subcompMark_model
    {X : Type} [Group X] (hX : E6FourSubcompMark X) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ lab.n = 2 ∧
      ((lab.tag = .twD ∧ lab.rank = 4) ∨ (lab.tag = .A ∧ lab.rank = 5)) ∧
      MarkedModel lab (X ⧸ Subgroup.center X) := by
  unfold E6FourSubcompMark at hX
  obtain ⟨lab, hlab, R, instR, I, F, θ, -, -, hP, hm⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel hX
  letI : Group R := instR
  exact ⟨lab, hlab, hP.1, hP.2, MarkedModel.of_mulEquiv θ.symm hm⟩

end CFSG.Assembly

end
