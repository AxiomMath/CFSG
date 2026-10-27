module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

namespace Up34Exc


@[expose] def cop (τ : Tag) (γ δ : Fin τ.rank → ℤ) : ℤ := 2 * iform γ δ / iform γ γ

@[expose] def a2Exp (τ : Tag) (γ₁ γ₂ : Fin τ.rank → ℤ) (j : Fin τ.rank) : ℤ :=
  cop τ γ₁ (Pi.single j 1) + 2 * cop τ γ₂ (Pi.single j 1)

@[expose] def IsA2Pair (τ : Tag) (γ₁ γ₂ : Fin τ.rank → ℤ) : Prop :=
  IsRoot τ γ₁ ∧ IsRoot τ γ₂ ∧ iform γ₁ γ₁ = iform γ₂ γ₂ ∧ 2 * iform γ₁ γ₂ = - iform γ₁ γ₁

@[expose] def RDSize (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [CharP L 2] (a : Fin τ.rank → Lˣ), (∀ j, a j ^ 3 = 1) →
    ∀ i : KernelComponent (rootCharHom a),
      (componentRoots (rootCharHom a) i).ncard = 2 ∨ (componentRoots (rootCharHom a) i).ncard = 6 ∨
        14 ≤ (componentRoots (rootCharHom a) i).ncard

@[expose] def RDGlue (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [CharP L 2] (a : Fin τ.rank → Lˣ), (∀ j, a j ^ 3 = 1) →
    ∀ i : KernelComponent (rootCharHom a), (componentRoots (rootCharHom a) i).ncard = 6 →
      ∃ γ₁ γ₂ : Fin τ.rank → ℤ, IsA2Pair τ γ₁ γ₂ ∧
        componentRoots (rootCharHom a) i = {γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)} ∧
        ∀ ω : Lˣ, ω ^ 3 = 1 → ω ≠ 1 →
          ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ j, a j = ω ^ (ε * a2Exp τ γ₁ γ₂ j)

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
