module

public import CFSG.CGT.T75H.Split
public import CFSG.CGT.T75H.SylowData

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75

@[expose] def Step69Rank2 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Nat.card T = 4 →
    ∀ S : Sylow 2 G, SylowData T T₁ S →
      ∀ α ∈ Cbar T T₁ S, ∀ β ∈ Cbar T T₁ S, α ≠ 1 → β ≠ 1 → α ≠ β → α * α = 1 → β * β = 1 →
        α * β = β * α → False

end CFSG.CGT.T75H
