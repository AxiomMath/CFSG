module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR3A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

variable {X : Type} [Group X]

open Subgroup

structure Z4IPartB (N Q Y V V' B K : Subgroup X) : Prop where
  odd_N : Odd (Nat.card N)
  N_le_K : N ≤ K
  Q_comm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  card_Q : Nat.card Q = 64
  normal_Q : ∀ g x : X, x ∈ Q → g * x * g⁻¹ ∈ Q
  cent_Q : ∀ g : X, (∀ q ∈ Q, g * q = q * g) → g ∈ Q ⊔ N
  Q_le_K : Q ≤ K
  relIndex_K : (Q ⊔ N).relIndex K = 4
  Q_eq : Q = B ⊔ V'
  B_le_Q : B ≤ Q
  Y_le_Q : Y ≤ Q
  Y_eq : Y = V ⊔ V'
  V_inf_V' : V ⊓ V' = ⊥
  card_V : Nat.card V = 4
  card_V' : Nat.card V' = 4
  sq_mem_V : ∀ q ∈ Q, q ^ 2 ∈ V
  K_cent_Y : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k
  comm_KQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ V
  card_B : Nat.card B = 16
  Y_sq : ∀ y ∈ Y, y * y = 1
  normal_Y : ∀ g x : X, x ∈ Y → g * x * g⁻¹ ∈ Y
  normal_V : ∀ g x : X, x ∈ V → g * x * g⁻¹ ∈ V

structure Z4IPartC (N Q Y V V' B K : Subgroup X) (ρ t τ l : X) : Prop where
  rho_pow_three : ρ ^ 3 = 1
  rho_norm_Q : ∀ x ∈ Q, ρ * x * ρ⁻¹ ∈ Q
  rho_norm_Y : ∀ x ∈ Y, ρ * x * ρ⁻¹ ∈ Y
  rho_norm_V : ∀ x ∈ V, ρ * x * ρ⁻¹ ∈ V
  rho_norm_V' : ∀ x ∈ V', ρ * x * ρ⁻¹ ∈ V'
  rho_norm_B : ∀ x ∈ B, ρ * x * ρ⁻¹ ∈ B
  rho_norm_K : ∀ x ∈ K, ρ * x * ρ⁻¹ ∈ K
  rho_fpf_Q : ∀ q ∈ Q, ρ * q * ρ⁻¹ = q → q = 1
  rho_fpf_KQ : ∀ k ∈ K, ρ * k * ρ⁻¹ * k⁻¹ ∈ Q ⊔ N → k ∈ Q ⊔ N
  t_norm_K : ∀ k ∈ K, t * k * t⁻¹ ∈ K
  tau_norm_K : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K
  l_norm_K : ∀ k ∈ K, l * k * l⁻¹ ∈ K
  comm_t_K : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ Q ⊔ N
  tau_inv : ∀ q ∈ Q, τ * q * τ⁻¹ = q⁻¹
  tau_not_mem_Q : τ ∉ Q ⊔ N

structure Z4IPartD (N Q Y V V' B K : Subgroup X) (ρ t τ l : X) : Prop where
  t_ne_one : t ≠ 1
  t_ne_tau : t ≠ τ
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
  Y_cent_t : ∀ y ∈ Y, t * y = y * t → y ∈ V
  bound : ∀ R : Subgroup X, IsPGroup 2 R → R ≤ centralizer ({t} : Set X) → Nat.card R ≤ 128
  not_conj : ∀ g : X, g * t * g⁻¹ ≠ t * τ

theorem Z4IData.of_parts {N Q Y V V' B K : Subgroup X} {ρ t τ l : X}
    (hB : Z4IPartB N Q Y V V' B K) (hC : Z4IPartC N Q Y V V' B K ρ t τ l)
    (hD : Z4IPartD N Q Y V V' B K ρ t τ l) : Z4IData N Q Y V V' B K ρ t τ l where
  odd_N := hB.odd_N
  N_le_K := hB.N_le_K
  Q_comm := hB.Q_comm
  card_Q := hB.card_Q
  normal_Q := hB.normal_Q
  cent_Q := hB.cent_Q
  Q_le_K := hB.Q_le_K
  relIndex_K := hB.relIndex_K
  Q_eq := hB.Q_eq
  B_le_Q := hB.B_le_Q
  Y_le_Q := hB.Y_le_Q
  Y_eq := hB.Y_eq
  V_inf_V' := hB.V_inf_V'
  card_V := hB.card_V
  card_V' := hB.card_V'
  sq_mem_V := hB.sq_mem_V
  K_cent_Y := hB.K_cent_Y
  comm_KQ := hB.comm_KQ
  card_B := hB.card_B
  Y_sq := hB.Y_sq
  normal_Y := hB.normal_Y
  normal_V := hB.normal_V
  rho_pow_three := hC.rho_pow_three
  rho_norm_Q := hC.rho_norm_Q
  rho_norm_Y := hC.rho_norm_Y
  rho_norm_V := hC.rho_norm_V
  rho_norm_V' := hC.rho_norm_V'
  rho_norm_B := hC.rho_norm_B
  rho_norm_K := hC.rho_norm_K
  rho_fpf_Q := hC.rho_fpf_Q
  rho_fpf_KQ := hC.rho_fpf_KQ
  t_norm_K := hC.t_norm_K
  tau_norm_K := hC.tau_norm_K
  l_norm_K := hC.l_norm_K
  comm_t_K := hC.comm_t_K
  tau_inv := hC.tau_inv
  tau_not_mem_Q := hC.tau_not_mem_Q
  t_ne_one := hD.t_ne_one
  t_ne_tau := hD.t_ne_tau
  t_sq := hD.t_sq
  tau_sq := hD.tau_sq
  l_sq := hD.l_sq
  t_tau := hD.t_tau
  t_l := hD.t_l
  tau_l := hD.tau_l
  t_rho := hD.t_rho
  tau_rho := hD.tau_rho
  l_rho := hD.l_rho
  B_cent_t := hD.B_cent_t
  cent_t_Q := hD.cent_t_Q
  V_cent_t := hD.V_cent_t
  Y_cent_t := hD.Y_cent_t
  bound := hD.bound
  not_conj := hD.not_conj

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
