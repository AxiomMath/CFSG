module

public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def LThmA : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ K ∈ Ω, ∀ L : Subgroup G, IsComponentOf L ⊤ → ∀ k ∈ K, conjSub k L = L

@[expose] def L17_3 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      (∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥) → (⨆ J ∈ Ω, J) = ⊤ →
        ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
          ∃ L : Subgroup G, IsComponentOf L ⊤ ∧ L.Normal ∧ z ∈ L ∧
            (∀ J ∈ Ω, ∀ t : G, IsUniqueInvolution J t → t ∉ L → Commutes K J) ∧
            (((∀ J ∈ Ω, ∃ g : G, conjSub g K = J) ∨
                ∀ J ∈ Ω, ∀ t : G, IsUniqueInvolution J t → t ∈ L) →
              IsSimpleGroup ↥L ∧ Subgroup.centralizer (L : Set G) = ⊥)

end CFSG.ClassicalInvolution.Asc77
