module

public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreStab
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

set_option linter.unusedSectionVars false


@[expose] def D5FixedSpinPerfect : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀)
    (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) → S.D.Φ = twistHom TwistTag.E6 L Fr →
    ((3 : ℕ) : L) ≠ 0 → 3 ∣ S.D.q + 1 → S.D.q ≠ 2 →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    (kernelRoots (rootCharHom a)).ncard = 40 →
      ⁅rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model,
          rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model⁆ =
        rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
