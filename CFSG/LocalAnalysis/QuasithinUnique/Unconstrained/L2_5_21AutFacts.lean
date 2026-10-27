module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small

public section

namespace CFSG.QuasithinUnique

structure OutAutFacts (X : Type) [Group X] : Prop where
  sq_inner : ∀ α : MulAut X, α * α ∈ innerAut X
  outer_conj : ∀ α β : MulAut X, α * α = 1 → β * β = 1 → α ∉ innerAut X → β ∉ innerAut X →
    ∃ φ : MulAut X, φ * α * φ⁻¹ = β
  odd_pair : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ a b : X, orderOf a = q → orderOf b = q →
    a * b = b * a → b ∈ Subgroup.zpowers a

end CFSG.QuasithinUnique
