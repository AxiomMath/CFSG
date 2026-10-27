module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Res
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPBasic
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)
open CFSG.LocalAnalysis.GLTheoremA.FP (fixNum)
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Lang


@[expose] def L154D4Class : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    rootDiagUnit τ a ∈ S.D.torus → (∀ k, a k ^ 3 = 1) → rootDiagUnit τ a ≠ 1 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    catalogIs (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) isD4any →
    compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24 ∧
      (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin τ.rank → ℤ) → _)

@[expose] def L154D4TwoPart : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (R : FrobRoot S.D 3) (e : ℕ) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    L154RootD0 S R → 1 ≤ e → R.q0 = 2 ^ e →
    rootDiagUnit τ a ∈ S.D.torus → (∀ k, a k ^ 3 = 1) → rootDiagUnit τ a ≠ 1 →
    R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    compRank (componentRoots (rootCharHom a) i) = 4 →
    (componentRoots (rootCharHom a) i).ncard = 24 →
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
    twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin τ.rank → ℤ) → _) →
    ∀ σ : MulAut ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      (∀ r, ((σ r : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) : ModGL τ L) =
        R.step0 (r : ModGL τ L)) →
      twoPart (fixNum (onCenterQuotient σ)) ^ 3 =
        twoPart (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)))

end Lang

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
