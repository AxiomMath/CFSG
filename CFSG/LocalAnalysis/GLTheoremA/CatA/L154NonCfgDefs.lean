module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgMark

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

section Defs


structure L154Cls {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (p : ℕ) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  torus : rootDiagUnit τ a ∈ S.D.torus
  pow : ∀ k, a k ^ p = 1
  ne_one : rootDiagUnit τ a ≠ 1
  qs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def L154ClassModel {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) : Prop :=
  L154NonCfgModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
    Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

@[expose] def L154NonCfgModels : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (p : ℕ) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    L154Cls S p a i → ¬ L154TypeAClass a i → ¬ L154E6Class a i → L154ClassModel S i

@[expose] def L154F4Models : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.F4 L p₀)
    (p : ℕ) (a : Fin Tag.F4.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    L154Cls S p a i →
    twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) →
    ((compRank (componentRoots (rootCharHom a) i) = 2 ∧
        (componentRoots (rootCharHom a) i).ncard = 8) ∨
      (compRank (componentRoots (rootCharHom a) i) = 3 ∧
        (componentRoots (rootCharHom a) i).ncard = 18)) →
    L154ClassModel S i

@[expose] def L154Rank4Models : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (p : ℕ) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    L154Cls S p a i →
    ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) →
    compRank (componentRoots (rootCharHom a) i) = 4 →
    (componentRoots (rootCharHom a) i).ncard = 24 → L154ClassModel S i

end Defs

section Reduction


theorem l154NonCfgOutdiag_of_models (h : L154NonCfgModels) : L154NonCfgOutdiag := by
  intro τ L _ _ _ p₀ S p a i hp hp2 hT hap h1 hqs hA hE
  exact l154_marking_of_nonCfgModel hqs hp hp2
    (h τ L p₀ S p a i ⟨hp, hp2, hT, hap, h1, hqs⟩ hA hE)

end Reduction

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
