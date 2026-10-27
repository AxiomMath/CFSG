module

public import CFSG.CGT.A8S.L2Eval
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.CGT.A8S.L2

structure T1ModelA8 (H : Type*) [Group H] where
  T0 : Subgroup H
  B0 : Subgroup H
  b0 : H
  d : Fin 2 → H
  theta : Fin 2 → H
  alpha : H ≃* H
  tau : H
  beta : H
  b0_mem : b0 ∈ B0
  d_mem : ∀ i, d i ∈ Subgroup.normalizer (B0 : Set H)
  theta_mem : ∀ i, theta i ∈ Subgroup.normalizer (B0 : Set H)
  alpha_T : ∀ x, x ∈ T0 ↔ alpha x ∈ T0
  alpha_alpha : ∀ x, alpha (alpha x) = x
  inv_class : ∀ x : H, x * x = 1 → x ∉ T0 → ∃ n : H, n * b0 * n⁻¹ = x ∨ n * alpha b0 * n⁻¹ = x
  klein_eq : ∀ B' : Subgroup H, b0 ∈ B' → (∀ x ∈ B', x * x = 1) → Nat.card B' = 4 →
    B' ⊓ T0 = ⊥ →
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
  theta_sq : ∃ w : Fin 2 → List (Fin 2), ∀ i,
    evalD (d 0) (d 1) (w i) = theta i ∧ evalD (theta 0) (theta 1) (w i) = d i
  tau_mem : tau ∈ T0
  tau_not : tau ∉ Subgroup.normalizer (B0 : Set H)
  beta_mem : beta ∈ B0
  beta_ne : beta ≠ 1
  comm_mem : tau * beta * tau⁻¹ * beta⁻¹ ∈ T0
  comm_norm : tau * beta * tau⁻¹ * beta⁻¹ ∈ Subgroup.normalizer (B0 : Set H)
  comm_ne : tau * beta * tau⁻¹ * beta⁻¹ ≠ 1
  sig_beta : d 1 * beta = beta * d 1
  sig_comm : d 1 * (tau * beta * tau⁻¹ * beta⁻¹) = (tau * beta * tau⁻¹ * beta⁻¹) * d 1
  sig_fix : ∀ y ∈ B0, d 1 * y = y * d 1 → y = 1 ∨ y = beta

end CFSG.CGT.A8S.L2
