module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Defs

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

structure Facts {G : Type*} [Group G] (L : Subgroup G) (t x : G) : Prop where
  card_J : Nat.card ↥(jOf L x) = 60
  card_Cx : Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) = 960
  J_le : jOf L x ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)
  J_normal :
    ((jOf L x).subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))).Normal
  J_center : ∀ j ∈ jOf L x, (∀ j' ∈ jOf L x, j * j' = j' * j) → j = 1
  card_Y : Nat.card ↥(centralizer (jOf L x : Set G) ⊓
    (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) = 8
  G3 : ∃ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G),
    ∃ y ∈ centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)), c * y * c⁻¹ * y⁻¹ = x
  G5 : ∀ z ∈ jOf L x, z ≠ 1 → z * z = 1 →
    ∃ k ∈ L, k * x * k⁻¹ = x * z ∧ jOf L x ⊔ (jOf L x).map (MulAut.conj k).toMonoidHom = L
  G1 : ∀ w ∈ centralizer ({t} : Set G), orderOf w = 2 → w ≠ t →
    ∃ c ∈ centralizer ({t} : Set G), c * w * c⁻¹ ∈ centralizer ({x} : Set G) ∧
      c * w * c⁻¹ ∉ centralizer (jOf L x : Set G)
  G2 : ∀ x' ∈ centralizer ({t} : Set G), orderOf x' = 2 →
    Nat.card ↥(centralizer ({x'} : Set G) ⊓ centralizer ({t} : Set G)) ∣ 960 →
    ∃ R : Subgroup G, R ≤ centralizer ({x'} : Set G) ⊓ centralizer ({t} : Set G) ∧
      ⁅R, R⁆ = R ∧ 60 ≤ Nat.card ↥R

structure Model {P : Type*} [Group P] (K D : Subgroup P) (t₀ x₀ : P) : Prop where
  D_le : D ≤ K
  card_J : Nat.card ↥(jOf D x₀) = 60
  card_Kx : Nat.card ↥(K ⊓ centralizer ({x₀} : Set P)) = 960
  J_normal : ((jOf D x₀).subgroupOf (K ⊓ centralizer ({x₀} : Set P))).Normal
  J_center : ∀ j ∈ jOf D x₀, (∀ j' ∈ jOf D x₀, j * j' = j' * j) → j = 1
  card_Y : Nat.card ↥(centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P))) = 8
  G3 : ∃ c ∈ K ⊓ centralizer ({x₀} : Set P),
    ∃ y ∈ centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)),
      c * y * c⁻¹ * y⁻¹ = x₀
  G5 : ∀ z ∈ jOf D x₀, z ≠ 1 → z * z = 1 →
    ∃ k ∈ D, k * x₀ * k⁻¹ = x₀ * z ∧ jOf D x₀ ⊔ (jOf D x₀).map (MulAut.conj k).toMonoidHom = D
  G1 : ∀ w ∈ K, orderOf w = 2 → w ≠ t₀ →
    ∃ c ∈ K, c * w * c⁻¹ ∈ centralizer ({x₀} : Set P) ∧
      c * w * c⁻¹ ∉ centralizer (jOf D x₀ : Set P)
  G2 : ∀ x' ∈ K, orderOf x' = 2 → Nat.card ↥(K ⊓ centralizer ({x'} : Set P)) ∣ 960 →
    ∃ R : Subgroup P, R ≤ K ⊓ centralizer ({x'} : Set P) ∧ ⁅R, R⁆ = R ∧ 60 ≤ Nat.card ↥R

end CFSG.EvenSporadicStandard.M12Std.PropA
