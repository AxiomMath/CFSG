module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

namespace TwE6UniqAbs

@[expose] def RatQuasiEq : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ), S.D.q = 2 → rootDiagUnit Tag.E6 a ∈ S.D.torus →
    (∀ i, a i ^ 3 = 1) → rootDiagUnit Tag.E6 a ≠ 1 →
    ∀ i j : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) j) →
        rationalComponent S.ρ S.Γ (rootCharHom a) i = rationalComponent S.ρ S.Γ (rootCharHom a) j

end TwE6UniqAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
