module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacE
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompRel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

namespace ExcUntw

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def RationalCatalogueExp
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) : Prop :=
  ∃ j : ℕ, (j = componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∨ j = 1) ∧
    CatalogueOver (ringChar L) (S.D.q ^ j) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def ExcUntwRationalCatalogueExpAt
    (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          RationalCatalogueExp S i

@[expose] def ExcUntwOuterDCatalogueExpAt
    (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard =
            2 * compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1)) →
        ¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) →
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          RationalCatalogueExp S i

@[expose] def ExcUntwOuterECatalogueExpAt
    (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀),
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        6 ≤ compRank (componentRoots (rootCharHom a) i) →
        (componentRoots (rootCharHom a) i).ncard =
          eRootCount (compRank (componentRoots (rootCharHom a) i)) →
        ¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) →
          RationalCatalogueExp S i

end ExcUntw

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def TwistedE6RationalCatalogueExp :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀),
    (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr) →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ i, a i ^ p = 1) →
      rootDiagUnit Tag.E6 a ≠ 1 →
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ExcUntw.RationalCatalogueExp S i

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
