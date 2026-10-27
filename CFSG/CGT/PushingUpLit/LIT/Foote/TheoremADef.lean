module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Blocks

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit

@[expose] def FooteTheoremA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), QBlock K →
    ∀ y : G, y ∈ Subgroup.normalizer (K : Set G) → (∃ n : ℕ, y ^ 2 ^ n = 1) →
      y * y ∈ Subgroup.centralizer (blockU K : Set G) →
        ∃ a ∈ blockU K, a * y = y * a ∧ ∃ k ∈ K, a * k ≠ k * a

end CFSG.CGT.PushingUpLit.LIT.Foote
