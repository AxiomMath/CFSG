module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def KAU3I5 : Prop :=
  ∀ (p f : ℕ) (F : Type) [Field F] [Finite F], p.Prime → p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f →
    Nat.card F = (p ^ f) ^ 2 → ∀ (Y : Type) [Group Y] [Finite Y],
      Nonempty (Y ≃* StatedProj (StatedSU 3 (p ^ f) F)) → ∀ α : MulAut Y, α ∈ innSub Y →
        α * α = 1 → α ≠ 1 → KAAll α

@[expose] def KAU3I3 : Prop :=
  ∀ (p f : ℕ) (F : Type) [Field F] [Finite F], p.Prime → p ≠ 2 → 1 ≤ f → p ^ f = 3 →
    Nat.card F = (p ^ f) ^ 2 → ∀ (Y : Type) [Group Y] [Finite Y],
      Nonempty (Y ≃* StatedProj (StatedSU 3 (p ^ f) F)) → ∀ α : MulAut Y, α ∈ innSub Y →
        α * α = 1 → α ≠ 1 → KAAll α

@[expose] def KAU3II5 : Prop :=
  ∀ (p f : ℕ) (F : Type) [Field F] [Finite F], p.Prime → p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f →
    Nat.card F = (p ^ f) ^ 2 → ∀ (Y : Type) [Group Y] [Finite Y],
      Nonempty (Y ≃* StatedProj (StatedSU 3 (p ^ f) F)) → ∀ α : MulAut Y, α ∉ innSub Y →
        α * α = 1 → KAAll α

@[expose] def KAU3II3 : Prop :=
  ∀ (p f : ℕ) (F : Type) [Field F] [Finite F], p.Prime → p ≠ 2 → 1 ≤ f → p ^ f = 3 →
    Nat.card F = (p ^ f) ^ 2 → ∀ (Y : Type) [Group Y] [Finite Y],
      Nonempty (Y ≃* StatedProj (StatedSU 3 (p ^ f) F)) → ∀ α : MulAut Y, α ∉ innSub Y →
        α * α = 1 → KAAll α

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
