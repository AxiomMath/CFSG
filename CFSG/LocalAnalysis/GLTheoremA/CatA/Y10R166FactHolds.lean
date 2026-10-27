module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamDFour2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166F4Model3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamE7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamE8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamTwA5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B17
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamA5Four2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamE6Four3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamA8Two3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Iso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralFrames
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Levi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwARigid
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutFacts
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowFieldCover
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwapRee
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicSix
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatOmegaMinusSporadic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterOmegaExc
public import CFSG.Quasithin.Vol2.Ch4Sec4W443
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.Quasithin.Vol2.KGFact4413Borel
public import CFSG.Timmesfeld.Bridge.RootSetsSyl
public import CFSG.Timmesfeld.Bridge.RootStructODBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open


theorem i166Fact_holds : I166Fact := by
  classical
  have htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J :=
    fun {K R} _ _ _ _ e {p} h => exists_concl166S_of_mulEquiv e h
  exact i166Fact_of_families (i166On_famB_of_transport htr)
    (i166On_famD_of_transport htr (i166On_famDFive_holds htr))
    (i166On_famF4_of_transport htr)
    (i166On_famE7_of_transport htr layerData166At_D_six)
    (i166On_famE8_of_transport htr layerData166At_D_seven)
    i166On_famTwA5_holds i166On_famTwE6_holds
    (i166On_famA5Four_of_transport htr) (i166On_famE6Four_of_transport htr)
    (i166On_famA8Two_of_transport htr)

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
