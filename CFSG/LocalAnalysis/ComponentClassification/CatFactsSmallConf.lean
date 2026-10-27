module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Data

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups Subgroup
open CFSG.ComponentClassification.GSThmB

structure Q3ConfData (K₀ : Type) [Group K₀] (G : Type) [Group G] extends Q3ModelData K₀ G where
  τ₀ : G
  τ_eq : τ₀ = s₀ * (g₀⁻¹ * s₀ * g₀)
  z₀ : G
  R₀ : Subgroup G
  g_coset : ∀ x ∈ M.A, (∀ q ∈ Q₀, x * q * x⁻¹ ∈ Q₀) → x ∉ Q₀ → g₀⁻¹ * x ∈ Q₀
  τ_Q : ∀ q ∈ Q₀, τ₀ * q = q * τ₀
  z_unique : ∀ w ∈ Q₀ ⊓ L, (∀ v ∈ Q₀ ⊓ L, w * v = v * w) → w * w = 1 → w ≠ 1 → w = z₀
  R_unique : ∀ R' : Subgroup G, R' ≤ M.A → Nat.card R' = 128 → Q₀ ≤ R' → g₀ ∈ R' → R' = R₀
  R_le : R₀ ≤ M.A
  card_A : ∃ m, Odd m ∧ Nat.card M.A = 2 ^ 7 * m
  card_D : Nat.card ↥(Q₀ ⊓ L) = 8 ∧ Nat.card R₀ = 128
  Q_eq : Q₀ = Q₀ ⊓ L ⊔ zpowers τ₀ ⊔ zpowers s₀
  fix_τ : Nat.card ↥(L ⊓ centralizer ({τ₀} : Set G)) = 24
  g_z : g₀⁻¹ * z₀ * g₀ = z₀
  z_Q : ∀ q ∈ Q₀, z₀ * q = q * z₀
  T₀ : Subgroup G
  T_le : T₀ ≤ M.A ⊓ centralizer ({τ₀ * z₀} : Set G)
  card_T : Nat.card T₀ = 128
  card_Ctz : ∃ m, Odd m ∧ Nat.card ↥(M.A ⊓ centralizer ({τ₀ * z₀} : Set G)) = 2 ^ 7 * m
  tz_comm : τ₀ * z₀ ∈ ⁅T₀, T₀⁆
  z_τ : ∃ k ∈ M.P, k⁻¹ * z₀ * k = τ₀
  card_R0 : Nat.card ↥(R₀ ⊓ centralizer ({z₀} : Set G)) = 64
  card_Cz : ∃ m, Odd m ∧ Nat.card ↥(M.A ⊓ centralizer ({z₀} : Set G)) = 2 ^ 6 * m
  R0_decomp : ∃ D₁ D₂ : Subgroup G, D₁ ⊔ D₂ = R₀ ⊓ centralizer ({z₀} : Set G) ∧ D₁ ⊓ D₂ = ⊥ ∧
    D₁ ≤ centralizer (D₂ : Set G) ∧ Nonempty (D₁ ≃* DihedralGroup 4) ∧
    Nonempty (D₂ ≃* DihedralGroup 4) ∧ center D₁ = (zpowers z₀).subgroupOf D₁ ∧
    center D₂ = (zpowers τ₀).subgroupOf D₂
  R0_center : (center ↥(R₀ ⊓ centralizer ({z₀} : Set G))).map
      (R₀ ⊓ centralizer ({z₀} : Set G)).subtype = zpowers z₀ ⊔ zpowers τ₀ ∧
    closure {y | ∃ x ∈ R₀ ⊓ centralizer ({z₀} : Set G), y = x * x} = zpowers z₀ ⊔ zpowers τ₀
  R0_gen : closure {y | ∃ E : Subgroup G, E ≤ R₀ ⊓ centralizer ({z₀} : Set G) ∧
    Cat8.IsElemAb2 E ∧ Nat.card E = 16 ∧ y ∈ E} = R₀ ⊓ centralizer ({z₀} : Set G)
  E0 : ∃ E₀ : Subgroup G, E₀ ≤ R₀ ⊓ M.P ∧ Cat8.IsElemAb2 E₀ ∧ Nat.card E₀ = 16 ∧
    (∀ E' : Subgroup G, E' ≤ R₀ ⊓ M.P → Cat8.IsElemAb2 E' → Nat.card E' = 16 → E' = E₀) ∧
    z₀ ∈ E₀ ∧ τ₀ ∈ E₀ ∧ M.A ⊓ centralizer (E₀ : Set G) = E₀ ∧
    (∀ w ∈ E₀, w = 1 ∨ w ∈ Cat8.conjOrbit (M.A ⊓ normalizer (E₀ : Set G)) z₀ ∨
      w ∈ Cat8.conjOrbit (M.A ⊓ normalizer (E₀ : Set G)) (z₀ * τ₀)) ∧
    ((Nat.card ↥(M.A ⊓ normalizer (E₀ : Set G)) = 1920 ∧
        Nat.card (Cat8.conjOrbit (M.A ⊓ normalizer (E₀ : Set G)) z₀) = 10 ∧
        Nat.card (Cat8.conjOrbit (M.A ⊓ normalizer (E₀ : Set G)) (z₀ * τ₀)) = 5 ∧
        closure (Cat8.conjOrbit (M.A ⊓ normalizer (E₀ : Set G)) (z₀ * τ₀)) = E₀) ∨
      (Nat.card ↥(M.A ⊓ normalizer (E₀ : Set G)) = 1152 ∧
        Nat.card (Cat8.conjOrbit (M.A ⊓ normalizer (E₀ : Set G)) z₀) = 6 ∧
        Nat.card (Cat8.conjOrbit (M.A ⊓ normalizer (E₀ : Set G)) (z₀ * τ₀)) = 9 ∧
        closure {y | ∃ u ∈ Cat8.conjOrbit (M.A ⊓ normalizer (E₀ : Set G)) z₀,
          ∃ v ∈ Cat8.conjOrbit (M.A ⊓ normalizer (E₀ : Set G)) z₀, y = u * v} = E₀)) ∧
    (∀ A' : Subgroup G, A' ≤ R₀ → Cat8.IsElemAb2 A' → Nat.card A' = 16 →
      (∀ r ∈ R₀, ∀ x ∈ A', r * x * r⁻¹ ∈ A') → A' = E₀ ∨ ∃ w ∈ A', ∃ y ∈ M.A, y⁻¹ * s₀ * y = w) ∧
    Nat.card ↥(⁅E₀, zpowers s₀⁆ : Subgroup G) = 2 ∧
    ∃ e ∈ R₀ ⊓ M.P, e ∈ ⁅M.A ⊓ normalizer (E₀ : Set G), M.A ⊓ normalizer (E₀ : Set G)⁆ ∧
      e * e = 1 ∧ e ∉ centralizer (E₀ : Set G)
  Z_R : (center R₀).map R₀.subtype = zpowers (τ₀ * z₀)
  no_E32 : ∀ A' : Subgroup G, A' ≤ R₀ → Cat8.IsElemAb2 A' → Nat.card A' ≠ 32
  outer : ∀ y ∈ M.A, y * y = 1 → y ∉ M.P →
    (∃ k ∈ M.A, k⁻¹ * s₀ * k = y) ∨ ∃ k ∈ M.A, k⁻¹ * (s₀ * z₀ * τ₀) * k = y
  inner : ∀ y ∈ M.P, y * y = 1 → y ≠ 1 →
    (∃ k ∈ M.P, k⁻¹ * z₀ * k = y) ∨ ∃ k ∈ M.P, k⁻¹ * (z₀ * τ₀) * k = y

end CFSG.ComponentClassification.CatFactsSmall
