module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.CGT.M24R

structure T1Model8 (H : Type*) [Group H] (n : ℕ) where
  T0 : Subgroup H
  B0 : Subgroup H
  b0 : H
  d : Fin n → H
  theta : Fin n → H
  b0_mem : b0 ∈ B0
  d_mem : ∀ i, d i ∈ Subgroup.normalizer (B0 : Set H)
  theta_mem : ∀ i, theta i ∈ Subgroup.normalizer (B0 : Set H)
  inv_class : ∀ x : H, x * x = 1 → x ∉ T0 → ∀ A' : Subgroup H, Nat.card A' ≤ 4 →
    (∀ t ∈ T0, t * x = x * t → t ∈ A') → ∃ n : H, n * b0 * n⁻¹ = x
  klein_eq : ∀ B' : Subgroup H, b0 ∈ B' → (∀ x ∈ B', x * x = 1) → Nat.card B' = 4 →
    B' ⊓ T0 = ⊥ → Nat.card ↥(T0 ⊓ Subgroup.normalizer (B' : Set H)) = 4 →
    (∀ a ∈ T0 ⊓ Subgroup.normalizer (B' : Set H), ∀ x ∈ B', a * x = x * a) →
    (∀ b ∈ B', b ≠ 1 → ∀ y : H, y * b = b * y → y ∈ Subgroup.normalizer (B' : Set H)) →
    B' = B0
  swap : ∀ f : H → H,
    (∀ x ∈ Subgroup.normalizer (B0 : Set H), f x ∈ Subgroup.normalizer (B0 : Set H)) →
    (∀ x ∈ Subgroup.normalizer (B0 : Set H), ∀ y ∈ Subgroup.normalizer (B0 : Set H),
      f (x * y) = f x * f y) →
    (∀ x ∈ Subgroup.normalizer (B0 : Set H), ∀ y ∈ Subgroup.normalizer (B0 : Set H),
      f x = f y → x = y) →
    (∀ a ∈ Subgroup.normalizer (B0 : Set H), a ∈ T0 → f a ∈ B0) → (∀ b ∈ B0, f b ∈ T0) →
    ∃ e ∈ Subgroup.normalizer (B0 : Set H), ∀ i, e * f (d i) * e⁻¹ = theta i
  center : ∀ z : H, z ∈ Subgroup.normalizer (B0 : Set H) → (∀ i, z * d i = d i * z) → z = 1
  theta_sq : ∃ w : Fin n → List (Fin n × Bool), ∀ i,
    FreeGroup.lift d (FreeGroup.mk (w i)) = theta i ∧
      FreeGroup.lift theta (FreeGroup.mk (w i)) = d i

end CFSG.CGT.M24R
