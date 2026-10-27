module

public import CFSG.LocalAnalysis.Asc75.Data
public import CFSG.LocalAnalysis.Asc75.Fixed

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

@[expose] def Asc75Endgame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S A₁ A₂ H : Subgroup G), Hyp S A₁ A₂ H → A₁ ⊓ A₂ = ⊥ →
    H ≠ ⊤ → (∀ a ∈ uSet A₁ A₂, a ≠ 1 → FixedOnlyElt H a) →
    (∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂, a₁ ≠ 1 → a₂ ≠ 1 → a₁ * a₁ = 1 → a₂ * a₂ = 1 →
      FixedOnlyElt H (a₁ * a₂)) → False

end CFSG.Asc75
