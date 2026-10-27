module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighGraph
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.Lattice


@[expose] def RankFourGraphTwist : Prop :=
  ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ}, rootDiagUnit τ a ∈ S.D.torus →
    ∀ (i : KernelComponent (rootCharHom a)),
      twistKind S.ρ (rootCharHom a) i = .twoD →
      compRank (componentRoots (rootCharHom a) i) = 4 →
      (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i →
      (∀ β ∈ componentRoots (rootCharHom a) i, iform β β = 2) →
      ∃ v ∈ componentWeylGroup (componentRoots (rootCharHom a) i),
        (∀ γ ∈ componentRoots (rootCharHom a) i,
          S.rhoTwist v γ ∈ componentRoots (rootCharHom a) i) ∧
        (∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
          S.rhoTwist v γ ∈ posRoots (componentRoots (rootCharHom a) i)) ∧
        IsGraphTwist (componentRoots (rootCharHom a) i) (S.rhoTwist v)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
