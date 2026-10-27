module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def AnyKindCommuteThreeFull : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p),
    SimplyLacedTag τ → S.D.q = 3 → ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus →
    ∀ i : KernelComponent (rootCharHom a),
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 →
        2 < (componentRoots (rootCharHom a) i).ncard) →
      ∀ z : ModGL τ L, (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) →
        ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g

end CFSG.HardMathSupport.Timmesfeld.CrossChar
