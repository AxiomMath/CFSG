module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus


@[expose] def E6CentralizerConnOdd : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀),
    (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧
      S.D.Φ = Units.map (entrywiseHom Fr)) →
    ¬ 3 ∣ S.D.q - 1 → ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus →
      (∀ j, a j ^ 3 = 1) → ∀ y ∈ toralCentralizer Tag.E6 L a, S.D.step y = y →
        y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a))

@[expose] def E6CentralizerConnOddExcKernels : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀),
    (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧
      S.D.Φ = Units.map (entrywiseHom Fr)) →
    ¬ 3 ∣ S.D.q - 1 → ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus →
      (∀ j, a j ^ 3 = 1) →
      ((kernelRoots (rootCharHom a)).ncard = 18 ∨
        (kernelRoots (rootCharHom a)).ncard = 24) →
      ∀ y ∈ toralCentralizer Tag.E6 L a, S.D.step y = y →
        y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
