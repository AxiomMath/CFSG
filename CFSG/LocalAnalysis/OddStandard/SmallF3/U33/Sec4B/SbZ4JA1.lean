module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X]

structure Z4JData (N Q Y V V' B : Subgroup X) (ρ t τ l y z v₁ v₂ : X) : Prop where
  odd_N : Odd (Nat.card N)
  Q_comm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  card_Q : Nat.card Q = 64
  normal_Q : ∀ g x : X, x ∈ Q → g * x * g⁻¹ ∈ Q
  cent_Q : ∀ g : X, (∀ q ∈ Q, g * q = q * g) → g ∈ Q ⊔ N
  Q_eq : Q = B ⊔ V'
  B_le_Q : B ≤ Q
  Y_le_Q : Y ≤ Q
  Y_eq : Y = V ⊔ V'
  V_inf_V' : V ⊓ V' = ⊥
  card_V : Nat.card V = 4
  card_V' : Nat.card V' = 4
  card_B : Nat.card B = 16
  sq_mem_V : ∀ q ∈ Q, q ^ 2 ∈ V
  Y_sq : ∀ u ∈ Y, u * u = 1
  Y_mem : ∀ q ∈ Q, q * q = 1 → q ∈ Y
  normal_Y : ∀ g x : X, x ∈ Y → g * x * g⁻¹ ∈ Y
  normal_V : ∀ g x : X, x ∈ V → g * x * g⁻¹ ∈ V
  V_eq : V = closure {y, z}
  V'_eq : V' = closure {v₁, v₂}
  y_ne_one : y ≠ 1
  z_ne_one : z ≠ 1
  y_ne_z : y ≠ z
  v₁_ne_one : v₁ ≠ 1
  v₂_ne_one : v₂ ≠ 1
  v₁_ne_v₂ : v₁ ≠ v₂
  rho_pow_three : ρ ^ 3 = 1
  rho_norm_Q : ∀ x ∈ Q, ρ * x * ρ⁻¹ ∈ Q
  rho_norm_Y : ∀ x ∈ Y, ρ * x * ρ⁻¹ ∈ Y
  rho_norm_V : ∀ x ∈ V, ρ * x * ρ⁻¹ ∈ V
  rho_norm_V' : ∀ x ∈ V', ρ * x * ρ⁻¹ ∈ V'
  rho_norm_B : ∀ x ∈ B, ρ * x * ρ⁻¹ ∈ B
  rho_fpf_Q : ∀ q ∈ Q, ρ * q * ρ⁻¹ = q → q = 1
  tau_inv : ∀ q ∈ Q, τ * q * τ⁻¹ = q⁻¹
  tau_not_mem_Q : τ ∉ Q ⊔ N
  t_ne_one : t ≠ 1
  t_sq : t * t = 1
  tau_sq : τ * τ = 1
  l_sq : l * l = 1
  t_tau : t * τ = τ * t
  t_l : t * l = l * t
  tau_l : τ * l = l * τ
  t_rho : t * ρ = ρ * t
  tau_rho : τ * ρ = ρ * τ
  l_rho : l * ρ * l⁻¹ = ρ⁻¹
  B_cent_t : ∀ b ∈ B, t * b = b * t
  cent_t_Q : ∀ q ∈ Q, t * q = q * t → q ∈ B
  V_cent_t : ∀ v ∈ V, t * v = v * t
  Y_cent_t : ∀ u ∈ Y, t * u = u * t → u ∈ V
  t_v₁ : t * v₁ * t⁻¹ = v₁ * y
  t_v₂ : t * v₂ * t⁻¹ = v₂ * (y * z)
  l_y : l * y * l⁻¹ = y * z
  l_z : l * z * l⁻¹ = z
  lt_v₁ : (l * t) * v₁ * (l * t)⁻¹ = v₂

variable {H : Type} [Group H] [Finite H]

structure ZJBase (Q Y V V' B : Subgroup H) (ρ t τ l y z v₁ v₂ : H) : Prop where
  Q_comm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  card_Q : Nat.card Q = 64
  normal_Q : ∀ g x : H, x ∈ Q → g * x * g⁻¹ ∈ Q
  cent_Q : ∀ g : H, (∀ q ∈ Q, g * q = q * g) → g ∈ Q
  Q_eq : Q = B ⊔ V'
  B_le_Q : B ≤ Q
  Y_le_Q : Y ≤ Q
  Y_eq : Y = V ⊔ V'
  V_inf_V' : V ⊓ V' = ⊥
  card_V : Nat.card V = 4
  card_V' : Nat.card V' = 4
  card_B : Nat.card B = 16
  sq_mem_V : ∀ q ∈ Q, q ^ 2 ∈ V
  Y_sq : ∀ u ∈ Y, u * u = 1
  Y_mem : ∀ q ∈ Q, q * q = 1 → q ∈ Y
  normal_Y : ∀ g x : H, x ∈ Y → g * x * g⁻¹ ∈ Y
  normal_V : ∀ g x : H, x ∈ V → g * x * g⁻¹ ∈ V
  V_eq : V = closure {y, z}
  V'_eq : V' = closure {v₁, v₂}
  y_ne_one : y ≠ 1
  z_ne_one : z ≠ 1
  y_ne_z : y ≠ z
  v₁_ne_one : v₁ ≠ 1
  v₂_ne_one : v₂ ≠ 1
  v₁_ne_v₂ : v₁ ≠ v₂
  rho_pow_three : ρ ^ 3 = 1
  rho_norm_Q : ∀ x ∈ Q, ρ * x * ρ⁻¹ ∈ Q
  rho_norm_Y : ∀ x ∈ Y, ρ * x * ρ⁻¹ ∈ Y
  rho_norm_V : ∀ x ∈ V, ρ * x * ρ⁻¹ ∈ V
  rho_norm_V' : ∀ x ∈ V', ρ * x * ρ⁻¹ ∈ V'
  rho_norm_B : ∀ x ∈ B, ρ * x * ρ⁻¹ ∈ B
  rho_fpf_Q : ∀ q ∈ Q, ρ * q * ρ⁻¹ = q → q = 1
  tau_inv : ∀ q ∈ Q, τ * q * τ⁻¹ = q⁻¹
  tau_not_mem_Q : τ ∉ Q
  t_ne_one : t ≠ 1
  t_sq : t * t = 1
  tau_sq : τ * τ = 1
  l_sq : l * l = 1
  t_tau : t * τ = τ * t
  t_l : t * l = l * t
  tau_l : τ * l = l * τ
  t_rho : t * ρ = ρ * t
  tau_rho : τ * ρ = ρ * τ
  l_rho : l * ρ * l⁻¹ = ρ⁻¹
  B_cent_t : ∀ b ∈ B, t * b = b * t
  cent_t_Q : ∀ q ∈ Q, t * q = q * t → q ∈ B
  V_cent_t : ∀ v ∈ V, t * v = v * t
  Y_cent_t : ∀ u ∈ Y, t * u = u * t → u ∈ V
  t_v₁ : t * v₁ * t⁻¹ = v₁ * y
  t_v₂ : t * v₂ * t⁻¹ = v₂ * (y * z)
  l_y : l * y * l⁻¹ = y * z
  l_z : l * z * l⁻¹ = z
  lt_v₁ : (l * t) * v₁ * (l * t)⁻¹ = v₂

structure ZJData (Q Y V V' B : Subgroup H) (ρ t τ l y z v₁ v₂ : H) : Prop extends
    ZJBase Q Y V V' B ρ t τ l y z v₁ v₂ where
  K_triv : ∀ k ∈ ⁅centralizer (Y : Set H), zpowers ρ⁆ ⊔ Q, t * k * t⁻¹ * k⁻¹ ∈ Q → k ∈ Q
  tt_sylow : ∀ P : Subgroup H, P ≤ centralizer ({ρ} : Set H) → IsPGroup 2 P →
    ∃ c ∈ centralizer ({ρ} : Set H), ∀ p ∈ P, c * p * c⁻¹ ∈ closure ({t, τ} : Set H)
  two_pow_ten : 2 ^ 10 ∣ Nat.card H

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
