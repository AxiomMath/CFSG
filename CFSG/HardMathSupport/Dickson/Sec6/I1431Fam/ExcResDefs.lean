module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

set_option linter.unusedSectionVars false


@[expose] def HasA2Pair (τ : Tag) (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  ∃ γ ∈ Ψ, ∃ δ ∈ Ψ, IsRoot τ (γ + δ) ∧ ¬ IsRoot τ (γ - δ) ∧ ¬ IsRoot τ ((2 : ℤ) • γ + δ) ∧
    ¬ IsRoot τ (γ + (2 : ℤ) • δ)

@[expose] def ExcKac (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L], (3 : L) ≠ 0 → ∀ a : Fin τ.rank → Lˣ,
    (∀ i, a i ^ 3 = 1) → rootDiagUnit τ a ≠ 1 →
      (∀ i : KernelComponent (rootCharHom a),
        (componentRoots (rootCharHom a) i).ncard = 2 ∨
          HasA2Pair τ (componentRoots (rootCharHom a) i)) ∧
      ((τ = .F4 ∨ τ = .E8) → ∀ i : KernelComponent (rootCharHom a),
        (componentRoots (rootCharHom a) i).ncard ≠ 2) ∧
      ((τ = .E6 ∨ τ = .E7) → ∀ i j : KernelComponent (rootCharHom a),
        (componentRoots (rootCharHom a) i).ncard = 2 →
        (componentRoots (rootCharHom a) j).ncard = 2 → i = j)

@[expose] def ExcTLInner (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 4 ≤ Nat.card K →
    ∀ (M : Type) [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
      (i : KernelComponent χ), HasA2Pair τ (componentRoots χ i) →
      Group.IsPerfect ↥(componentRootSpan K χ i) →
      ∀ q : ℕ, 10 ≤ q → ¬ IsTypeL2 q ↥(componentRootSpan K χ i)

@[expose] def ExcTLInnerTwo (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ (M : Type) [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
      (i : KernelComponent χ), HasA2Pair τ (componentRoots χ i) →
      Group.IsPerfect ↥(componentRootSpan K χ i) →
      ∀ q : ℕ, 10 ≤ q → ¬ IsTypeL2 q ↥(componentRootSpan K χ i)

@[expose] def ExcTLKind (k : TwistKind) (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      twistKind S.ρ (rootCharHom a) i = k →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      ∀ q : ℕ, 10 ≤ q → ¬ IsTypeL2 q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def ExcTLOther (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      twistKind S.ρ (rootCharHom a) i ≠ .inner →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      ∀ q : ℕ, 10 ≤ q → ¬ IsTypeL2 q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem excTLOther_of_kinds {τ : Tag} (h1 : ExcTLKind .suN τ) (h2 : ExcTLKind .twoD τ)
    (h3 : ExcTLKind .exc τ) : ExcTLOther τ := by
  intro L _ _ p₀ S a hT ha3 h1' i hk hQ q hq
  cases hk' : twistKind S.ρ (rootCharHom a) i with
  | inner => exact absurd hk' hk
  | suN => exact h1 L p₀ S a hT ha3 h1' i hk' hQ q hq
  | twoD => exact h2 L p₀ S a hT ha3 h1' i hk' hQ q hq
  | exc => exact h3 L p₀ S a hT ha3 h1' i hk' hQ q hq

end CFSG.HardMathSupport.Dickson.Sec6.I1431
