module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HStdExcl

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Rat


@[expose] def E6TwoRatNotSmall : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀), S.D.q = 2 →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
      rootDiagUnit Tag.E6 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          ¬ SmallOrd (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def E6TwoD4NotSmall : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀), S.D.q = 2 →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
      rootDiagUnit Tag.E6 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        compRank (componentRoots (rootCharHom a) i) = 4 →
        (componentRoots (rootCharHom a) i).ncard = 24 →
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          ¬ SmallOrd (rationalComponent S.ρ S.Γ (rootCharHom a) i)

end Rat

end CFSG.LocalAnalysis.GLTheoremA.HStdExcl

end
