module

public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.ABGLocalTools

@[expose] def QbarNoComponentOfAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (Q T N : Subgroup G), orderOf z = 2 →
    IsSylowOf 2 T (centralizer ({z} : Set G)) → Q ≤ T → z ∈ Q →
    (Nat.card Q = 2 ^ 7 ∨ Nat.card Q = 2 ^ 9) →
    (∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ zpowers z) →
    (∀ x ∈ Q, ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * x * h ∈ T → h⁻¹ * x * h ∈ Q) →
    N ≤ centralizer ({z} : Set G) → N ≤ normalizer (Q : Set G) →
    (∀ B : Subgroup G, zpowers z ≤ B → B < Q → N ≤ normalizer (B : Set G) → ∀ n : ℕ,
      ∃ k ∈ (derivedSeries N n).map N.subtype, ∃ x ∈ Q, k⁻¹ * x * k * x⁻¹ ∉ B) →
    QbarNoComponent z Q

@[expose] def GoldschmidtQO : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (Q T N : Subgroup G), orderOf z = 2 →
    IsSylowOf 2 T (centralizer ({z} : Set G)) → Q ≤ T → z ∈ Q →
    (Nat.card Q = 2 ^ 7 ∨ Nat.card Q = 2 ^ 9) →
    (∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ zpowers z) →
    (∀ x ∈ Q, ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * x * h ∈ T → h⁻¹ * x * h ∈ Q) →
    N ≤ centralizer ({z} : Set G) → N ≤ normalizer (Q : Set G) →
    (∀ B : Subgroup G, zpowers z ≤ B → B < Q → N ≤ normalizer (B : Set G) → ∀ n : ℕ,
      ∃ k ∈ (derivedSeries N n).map N.subtype, ∃ x ∈ Q, k⁻¹ * x * k * x⁻¹ ∉ B) →
    centralizer ({z} : Set G) ≤
      normalizer ((Q ⊔ AS76b.oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G)

theorem goldschmidtQO_of (hGA : Asc76X.GoldschmidtTheoremA) (h : QbarNoComponentOfAction) :
    GoldschmidtQO := by
  intro G _ _ z Q T N hz hT hQT hzQ hQ7 hQab hcl hNC hNQ hN
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  exact centralizer_le_normalizer_of_goldschmidt hGA hz2 hT hQT hzQ hQab hcl
    (h G z Q T N hz hT hQT hzQ hQ7 hQab hcl hNC hNQ hN)

end CFSG.ComponentClassification.AS81
