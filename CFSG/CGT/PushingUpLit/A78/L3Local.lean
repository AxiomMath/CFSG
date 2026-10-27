module

public import CFSG.Timmesfeld.ARS.Defs

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld.ARS

variable {G : Type} [Group G]

structure L3Local (G : Type) [Group G] (J V V₂ Z : Subgroup G) (e : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  three_le : 3 ≤ e
  pgroup : IsPGroup 2 J
  odd_index : ¬ 2 ∣ J.index
  card_J : Nat.card J = 2 ^ (3 * e)
  card_center_J : Nat.card (Subgroup.center J) = 2 ^ e
  le : V ≤ J
  normalizes : J ≤ Subgroup.normalizer (V : Set G)
  normalizes₂ : J ≤ Subgroup.normalizer (V₂ : Set G)
  ne : V ≠ V₂
  abelian : ∀ x ∈ V, ∀ y ∈ V, Commute x y
  sq : ∀ x ∈ V, x * x = 1
  card_V : Nat.card V = 2 ^ (2 * e)
  mem : ∀ A : Subgroup G, A ≤ J → (∀ x ∈ A, ∀ y ∈ A, Commute x y) → (∀ x ∈ A, x * x = 1) →
    Nat.card A = Nat.card V → A = V ∨ A = V₂
  Z_le : Z ≤ V
  card_Z : Nat.card Z = 2 ^ e
  ti : ∀ g : G, Z ⊓ conjSub Z g ≠ ⊥ → conjSub Z g = Z
  normal_J : ∀ n ∈ Subgroup.normalizer (Z : Set G), conjSub J n = J
  transitive : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 →
    ∃ m ∈ Subgroup.normalizer (V : Set G), m * v * m⁻¹ = w

end CFSG.CGT.PushingUpLit.A78
