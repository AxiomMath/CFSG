module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourE8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTri

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.Lattice

section RankFour

theorem twoDExcFixedPointsDatum_holds : TwoDExcFixedPointsDatum :=
  twoDExcFixedPointsDatum_of_graph rankFourGraphTwist_holds rankFourTwoDE8Stable_holds

theorem twoDExcFixedPointsPerfect_holds {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD) :
    TwoDExcFixedPointsPerfect S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
  twoDExcFixedPointsPerfect_holds_of_graph rankFourGraphTwist_holds rankFourTwoDE8Stable_holds
    S hT i hkind

section Triality

theorem twoDExcFixedPointsPerfectAll_holds : TwoDExcFixedPointsPerfectAll :=
  twoDExcFixedPointsPerfectAll_of_data twoDExcFixedPointsDatum_holds
    excRankFourTrialityPerfect_holds

end Triality

end RankFour

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
