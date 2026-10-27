module

public import CFSG.CGT.L5R.L2GBasicL

public section

namespace CFSG.CGT.L5R

@[expose] def IsAdmL {H : Type*} [Group H] (T0 B' : Subgroup H) : Prop :=
  (∀ x ∈ B', x * x = 1) ∧ Nat.card B' = 8 ∧ B' ⊓ T0 = ⊥ ∧
    (∀ a ∈ T0 ⊓ Subgroup.normalizer (B' : Set H), ∀ x ∈ B', a * x = x * a) ∧
    ∀ b ∈ B', b ≠ 1 → ∀ y : H, y * b = b * y → y ∈ Subgroup.normalizer (B' : Set H)

structure T1ModelL (H : Type*) [Group H] where
  T0 : Subgroup H
  B0 : Subgroup H
  b0 : H
  c0 : H
  d : Fin 2 → H
  theta : Fin 2 → H
  z1 : H
  z2 : H
  b0_mem : b0 ∈ B0
  b0_ne : b0 ≠ 1
  d_mem : ∀ i, d i ∈ Subgroup.normalizer (B0 : Set H)
  theta_mem : ∀ i, theta i ∈ Subgroup.normalizer (B0 : Set H)
  z1_mem : z1 ∈ Subgroup.normalizer (B0 : Set H)
  z2_mem : z2 ∈ Subgroup.normalizer (B0 : Set H)
  z1_conj : ∃ n : H, n * z1 * n⁻¹ ∈ B0
  z2_notMem : z2 ∉ T0
  z2_card : Nat.card ↥(T0 ⊓ Subgroup.centralizer ({z2} : Set H)) = 4
  inv_class : ∀ x : H, x * x = 1 → x ∉ T0 →
    Nat.card ↥(T0 ⊓ Subgroup.centralizer ({x} : Set H)) = 8 →
      (∃ n : H, n * b0 * n⁻¹ = x) ∨ ∃ n : H, n * c0 * n⁻¹ = x
  klein_eq : ∀ B' : Subgroup H, b0 ∈ B' → IsAdmL T0 B' → B' = B0
  klein_none : ∀ B' : Subgroup H, c0 ∈ B' → IsAdmL T0 B' → False
  swap : ∀ f : H → H,
    (∀ x ∈ Subgroup.normalizer (B0 : Set H), f x ∈ Subgroup.normalizer (B0 : Set H)) →
    (∀ x ∈ Subgroup.normalizer (B0 : Set H), ∀ y ∈ Subgroup.normalizer (B0 : Set H),
      f (x * y) = f x * f y) →
    (∀ x ∈ Subgroup.normalizer (B0 : Set H), ∀ y ∈ Subgroup.normalizer (B0 : Set H),
      f x = f y → x = y) →
    (∀ a ∈ Subgroup.normalizer (B0 : Set H), a ∈ T0 → f a ∈ B0) → (∀ b ∈ B0, f b ∈ T0) →
    (∀ m : H, m * f z1 * m⁻¹ ∈ T0 ∨
      Nat.card ↥(T0 ⊓ Subgroup.centralizer ({m * f z1 * m⁻¹} : Set H)) ≠ 4) →
    (∀ m n : H, n * b0 * n⁻¹ ≠ m * f z2 * m⁻¹) →
    ∃ e ∈ Subgroup.normalizer (B0 : Set H), ∀ i, e * f (d i) * e⁻¹ = theta i
  center : ∀ z : H, z ∈ Subgroup.normalizer (B0 : Set H) → (∀ i, z * d i = d i * z) → z = 1
  theta_sq : ∃ w : Fin 2 → List (Fin 2 × Bool), ∀ i,
    FreeGroup.lift d (FreeGroup.mk (w i)) = theta i ∧
      FreeGroup.lift theta (FreeGroup.mk (w i)) = d i

end CFSG.CGT.L5R
