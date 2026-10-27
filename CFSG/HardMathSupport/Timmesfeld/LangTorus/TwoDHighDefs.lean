module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar


@[expose] def TwoDHighComponents : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.E → rootDiagUnit τ a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .twoD →
      5 ≤ compRank (componentRoots (rootCharHom a) i) →
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def TwoDHighComponentsT : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ a ^ p = 1 →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      twistKind S.ρ (rootCharHom a) i = .twoD →
      5 ≤ compRank (componentRoots (rootCharHom a) i) →
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem twoDHighComponents_of_T (h : TwoDHighComponentsT) : TwoDHighComponents :=
  fun τ L _ _ p S a hE ha1 i hk h5 hbig =>
    h τ L p S a (S.E_le hE).1 (S.E_exp _ hE) ha1 i hk h5 hbig

end CFSG.HardMathSupport.Timmesfeld.LangTorus
