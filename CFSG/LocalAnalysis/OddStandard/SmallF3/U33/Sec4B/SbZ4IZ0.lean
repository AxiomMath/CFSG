module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IK0
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

structure ZEData (Q Y V V' B K : Subgroup H) (ρ t τ l : H) : Prop extends
    ZIKData Q Y V V' B K ρ where
  card_B : Nat.card B = 16
  Y_sq : ∀ y ∈ Y, y * y = 1
  normal_Q : ∀ g x : H, x ∈ Q → g * x * g⁻¹ ∈ Q
  normal_Y : ∀ g x : H, x ∈ Y → g * x * g⁻¹ ∈ Y
  normal_V : ∀ g x : H, x ∈ V → g * x * g⁻¹ ∈ V
  t_sq : t * t = 1
  tau_sq : τ * τ = 1
  l_sq : l * l = 1
  t_tau : t * τ = τ * t
  t_l : t * l = l * t
  tau_l : τ * l = l * τ
  t_rho : t * ρ = ρ * t
  tau_rho : τ * ρ = ρ * τ
  l_rho : l * ρ * l⁻¹ = ρ⁻¹
  t_norm_K : ∀ k ∈ K, t * k * t⁻¹ ∈ K
  tau_norm_K : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K
  l_norm_K : ∀ k ∈ K, l * k * l⁻¹ ∈ K
  comm_t_K : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ Q
  tau_inv : ∀ q ∈ Q, τ * q * τ⁻¹ = q⁻¹
  tau_not_mem_Q : τ ∉ Q
  B_cent_t : ∀ b ∈ B, t * b = b * t
  cent_t_Q : ∀ q ∈ Q, t * q = q * t → q ∈ B
  V_cent_t : ∀ v ∈ V, t * v = v * t
  Y_cent_t : ∀ y ∈ Y, t * y = y * t → y ∈ V
  bound : ∀ R : Subgroup H, IsPGroup 2 R → R ≤ centralizer ({t} : Set H) → Nat.card R ≤ 128
  not_conj : ∀ g : H, g * t * g⁻¹ ≠ t * τ

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
