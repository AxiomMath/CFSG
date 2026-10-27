module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterFix
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
open scoped Pointwise commutatorElement

section PerfectData

@[expose] def InnerD4FixedPointsPerfect : Prop :=
  ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ},
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (i : KernelComponent (rootCharHom a)),
      twistKind S.ρ (rootCharHom a) i = .inner →
      compRank (componentRoots (rootCharHom a) i) = 4 →
      (componentRoots (rootCharHom a) i).ncard = 24 →
      TwoDExcFixedPointsPerfect S a i
        (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))

end PerfectData

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
