module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

structure JankoSetting (G : Type) [Group G] [Finite G] (z : G) : Prop where
  orderOf_z : orderOf z = 2
  twoANine : IsTwoANine (centralizer ({z} : Set G))
  zbar_eq : (zbar (centralizer ({z} : Set G)) : G) = z
  isConj : ∀ u : G, orderOf u = 2 → IsConj u z
  odd_index : Odd (centralizer ({z} : Set G)).index
  twoANine_centralizer : ∀ u : G, orderOf u = 2 → IsTwoANine (centralizer ({u} : Set G))

structure JankoFrame (G : Type) [Group G] (z : G) where
  s₁ : G
  s₂ : G
  s₃ : G
  t : G
  ℓ : G
  P₁ : Subgroup G
  P₂ : Subgroup G
  P₃ : Subgroup G
  E : Subgroup G
  F : Subgroup G
  EF : Subgroup G
  F₁ : Subgroup G
  S₁ : Subgroup G
  P : Subgroup G
  K : Subgroup G
  L : Subgroup G
  L₁ : Subgroup G
  Q : Subgroup G
  D : Subgroup G
  V : Subgroup G
  P₁_eq : P₁ = zpowers s₁
  P₂_eq : P₂ = zpowers s₂
  P₃_eq : P₃ = zpowers s₃
  EF_eq : EF = E ⊓ F
  F₁_eq : F₁ = F ⊓ centralizer ({t} : Set G)
  L_eq : L = closure {ℓ, t}
  L₁_eq : L₁ = zpowers ℓ
  Q_eq : Q = closure {ℓ ^ 2, t * ℓ}
  D_eq : D = closure {t, ℓ ^ 2}
  V_eq : V = closure {t, z}
  orderOf_s₁ : orderOf s₁ = 3
  orderOf_s₂ : orderOf s₂ = 3
  orderOf_s₃ : orderOf s₃ = 3
  orderOf_t : orderOf t = 2
  t_mem : t ∈ centralizer ({z} : Set G)
  t_ne : t ≠ z
  orderOf_ℓ : orderOf ℓ = 8
  ℓ_pow_four : ℓ ^ 4 = z
  t_mul_ℓ : t * ℓ * t⁻¹ = ℓ ^ 3
  t_mul_s₁ : t * s₁ * t⁻¹ = s₁⁻¹
  ℓ_mem_F : ℓ ∈ F
  card_centralizer_s₁ :
    Nat.card (centralizer ({s₁} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 2160
  card_centralizer_s₂ :
    Nat.card (centralizer ({s₂} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 108
  card_centralizer_s₃ :
    Nat.card (centralizer ({s₃} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162
  exists_conj : ∀ x ∈ centralizer ({z} : Set G), x ^ 3 = 1 → x ≠ 1 →
    ∃ h ∈ centralizer ({z} : Set G), h * x * h⁻¹ = s₁ ∨ h * x * h⁻¹ = s₂ ∨ h * x * h⁻¹ = s₃
  exists_invert : ∀ s ∈ ({s₁, s₂, s₃} : Set G),
    ∃ b ∈ centralizer ({z} : Set G), orderOf b = 2 ∧ b * s * b⁻¹ = s⁻¹
  F_le : F ≤ centralizer ({z} : Set G)
  F_le_centralizer : F ≤ centralizer (P₁ : Set G)
  P₁_inf_F : P₁ ⊓ F = ⊥
  centralizer_P₁ : centralizer (P₁ : Set G) ⊓ centralizer ({z} : Set G) = P₁ ⊔ F
  card_F : Nat.card F = 720
  z_mem_F : z ∈ F
  eq_z_of_mem_F : ∀ x ∈ F, orderOf x = 2 → x = z
  z_mem_of_normal : ∀ B : Subgroup G, B ≤ F → F ≤ normalizer (B : Set G) → B ≠ ⊥ → z ∈ B
  card_le_of_odd : ∀ B : Subgroup G, B ≤ F → Odd (Nat.card B) → Nat.card B ≤ 9
  S₁_le : S₁ ≤ F
  S₁_quaternion : Nonempty (S₁ ≃* QuaternionGroup 4)
  card_EF : Nat.card EF = 9
  centralizer_EF : centralizer (EF : Set G) ⊓ F = EF ⊔ zpowers z
  normalizer_EF : normalizer (EF : Set G) ⊓ F = EF ⊔ L₁
  exists_even_card : ∀ y ∈ F, orderOf y = 3 →
    ∃ g ∈ F, Even (Nat.card (closure ({y, g * y * g⁻¹} : Set G)))
  t_mem_normalizer_F : t ∈ normalizer (F : Set G)
  card_F₁ : Nat.card F₁ = 24
  P₂_le_F₁ : P₂ ≤ F₁
  not_le_normalizer_P₂ : ¬ F₁ ≤ normalizer (P₂ : Set G)
  E_le : E ≤ centralizer ({z} : Set G)
  card_E : Nat.card E = 27
  E_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  E_pow_three : ∀ a ∈ E, a ^ 3 = 1
  E_eq_closure : E = closure {s₁, s₂, ℓ * s₂ * ℓ⁻¹}
  s₃_mem_E : s₃ ∈ E
  E_inf_centralizer_t : E ⊓ centralizer ({t} : Set G) = P₂
  centralizer_E : centralizer (E : Set G) ⊓ centralizer ({z} : Set G) = E ⊔ zpowers z
  centralizer_P₂ : centralizer (P₂ : Set G) ⊓ centralizer ({z} : Set G) = E ⊔ V
  D_le_normalizer : D ≤ normalizer (P₂ : Set G)
  card_normalizer_P₂ :
    Nat.card (normalizer (P₂ : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 216
  card_D : Nat.card D = 8
  D_center : ∀ x ∈ D, (∀ y ∈ D, x * y = y * x) → x = 1 ∨ x = z
  D_inf_centralizer : D ⊓ centralizer (P₂ : Set G) = V
  card_type_s₃_E : Nat.card {x : G // x ∈ E ∧
    Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162} = 8
  exists_ne_type_s₃ : ∀ B : Subgroup G, B ≤ E → Nat.card B = 9 →
    ∃ x ∈ B, x ≠ 1 ∧
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) ≠ 162
  K_le : K ≤ centralizer ({z} : Set G)
  card_K : Nat.card K = 48
  K_le_normalizer : K ≤ normalizer (E : Set G)
  E_inf_K : E ⊓ K = ⊥
  normalizer_E : normalizer (E : Set G) ⊓ centralizer ({z} : Set G) = E ⊔ K
  card_ne_three : ∀ B : Subgroup G, B ≤ K → K ≤ normalizer (B : Set G) → Nat.card B ≠ 3
  L_le_K : L ≤ K
  normalizer_E_inf_P₁ : normalizer (E : Set G) ⊓ normalizer (P₁ : Set G) ⊓
    centralizer ({z} : Set G) = E ⊔ L
  card_L : Nat.card L = 16
  L_inf_centralizer : L ⊓ centralizer (P₁ : Set G) = L₁
  mul_s₁_of_not_mem : ∀ x ∈ L, x ∉ L₁ → x * s₁ * x⁻¹ = s₁⁻¹
  eq_of_le_L : ∀ B : Subgroup G, B ≤ L → Nat.card B = 8 → t ∉ B → B = L₁ ∨ B = Q
  Q_quaternion : Nonempty (Q ≃* QuaternionGroup 2)
  eq_z_of_mem_Q : ∀ x ∈ Q, orderOf x = 2 → x = z
  P_le : P ≤ centralizer ({z} : Set G)
  card_P : Nat.card P = 81
  centralizer_P₃ : centralizer (P₃ : Set G) ⊓ centralizer ({z} : Set G) = P ⊔ zpowers z
  exists_orderOf_nine : ∃ x ∈ centralizer ({z} : Set G), orderOf x = 9
  exists_ne_comm : ∀ B : Subgroup G, B ≤ centralizer ({z} : Set G) → Nat.card B = 81 →
    ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a
  card_eq_of_odd : ∀ B : Subgroup G, B ≤ centralizer ({z} : Set G) → Odd (Nat.card B) →
    81 ∣ Nat.card B → Nat.card B = 81
  card_centralizer_inv : ∀ x ∈ centralizer ({z} : Set G), x ^ 3 = 1 →
    Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162 →
    ∀ b ∈ centralizer ({z} : Set G), orderOf b = 2 → b * x * b⁻¹ = x⁻¹ →
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G) ⊓
        centralizer ({z} : Set G) : Subgroup G) = 6
  card_centralizer_involution : ∀ u ∈ centralizer ({z} : Set G), orderOf u = 2 → u ≠ z →
    Nat.card (centralizer ({u} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 192
  type_s₂_of_involution : ∀ u ∈ centralizer ({z} : Set G), orderOf u = 2 → u ≠ z →
    ∀ x ∈ centralizer ({u} : Set G) ⊓ centralizer ({z} : Set G), x ^ 3 = 1 → x ≠ 1 →
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 108
  type_s₃_of_conj : ∀ B : Subgroup G, B ≤ centralizer ({z} : Set G) → Nat.card B = 9 →
    (∀ x ∈ B, ∀ y ∈ B, x ≠ 1 → y ≠ 1 → ∃ h ∈ centralizer ({z} : Set G), h * x * h⁻¹ = y) →
    ∀ x ∈ B, x ≠ 1 →
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162
  le_normalizer_E : ∀ X : Subgroup G, X ≤ centralizer ({z} : Set G) → Odd (Nat.card X) →
    E ≤ X → K ≤ normalizer (X : Set G) → X ≤ normalizer (E : Set G)

@[expose] def JankoFrameExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), orderOf z = 2 →
    IsTwoANine (centralizer ({z} : Set G)) → Nonempty (JankoFrame G z)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
