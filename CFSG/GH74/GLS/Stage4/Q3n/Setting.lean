module

public import CFSG.GH74.GLS.Stage4.RestCases

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest

structure Q3nSetting (G : Type) [Group G] [Finite G] (n : ℕ) where
  z : G
  z_ord : orderOf z = 2
  K₁ : Subgroup G
  K₂ : Subgroup G
  iso₁ : Nonempty (↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 n))
  iso₂ : Nonempty (↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 n))
  K_comm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x
  K_inter : K₁ ⊓ K₂ = Subgroup.zpowers z
  K_normal : ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ x ∈ K₁ ⊔ K₂, c * x * c⁻¹ ∈ K₁ ⊔ K₂
  U : Subgroup G
  U_card : Nat.card U = 4
  U_exp : ∀ x ∈ U, x * x = 1
  z_mem_U : z ∈ U
  C_eq : ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∃ x ∈ K₁ ⊔ K₂, ∃ y ∈ U, c = x * y
  P : Sylow 3 G
  P_le : (P : Subgroup G) ≤ K₁ ⊔ K₂
  H : Subgroup G
  Q : Subgroup G
  ε : ℤ
  k : ℕ
  ε_pm : ε = 1 ∨ ε = -1
  q_mod : (3 : ℤ) ^ n ≡ ε [ZMOD 4]
  k_eq : 2 * (k : ℤ) = 3 ^ n + ε
  H_comm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x
  U_le_H : U ≤ H
  Q_le_H : Q ≤ H
  U_inf_Q : U ⊓ Q = ⊥
  H_eq : H = U ⊔ Q
  Q_card : Nat.card Q = k ^ 2
  w₀ : G
  w₀_ord : orderOf w₀ = 2
  w₀_inv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹
  w₀_cent : ∀ x ∈ U, w₀ * x = x * w₀
  C0_eq : ∀ c ∈ Subgroup.centralizer (U : Set G), ∃ h ∈ H, c = h ∨ c = h * w₀
  W : Subgroup G
  W_iso : Nonempty (↥W ≃* DihedralGroup 6)
  W_norm_U : ∀ w ∈ W, w ∈ Subgroup.normalizer U
  w₀_mem_W : w₀ ∈ W
  w₀_central : ∀ w ∈ W, w * w₀ = w₀ * w
  N_eq : ∀ g ∈ Subgroup.normalizer U, ∃ h ∈ H, ∃ w ∈ W, g = h * w
  N_norm_H : ∀ g ∈ Subgroup.normalizer U, ∀ h ∈ H, g * h * g⁻¹ ∈ H
  a : G
  a_mem : a ∈ W
  a_ord : orderOf a = 3
  U_trans : ∀ x ∈ U, ∀ y ∈ U, x ≠ 1 → y ≠ 1 → ∃ g ∈ Subgroup.normalizer U, g * x * g⁻¹ = y
  nonsing : ∀ h ∈ H, a * h * a⁻¹ = h → h = 1
  inv_fix : ∀ y ∈ W, orderOf y = 2 → y ≠ w₀ →
    Nat.card {q : ↥Q // y * (q : G) * y⁻¹ = (q : G)} = k

@[expose] def Q3nSettingOf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 3 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
      Ch6Bad3 G → Nonempty (Q3nSetting G n)

end CFSG.GH74.GLS.Stage4.Q3n
