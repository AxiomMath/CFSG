module

public import CFSG.GH74.GLS.Stage4.T2Four
public import CFSG.GH74.GLS.Stage4.RestCases

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank

@[expose] def Ch6T2F1Gt9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 3 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
      Ch6Bad3 G → ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂],
        Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ →
          centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G))

@[expose] def Ch6P56bOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 2 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
      ∀ (z t : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂],
        Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
          ∀ (H : Subgroup G) (w₁ w₂ : G), T2Four z t K₁ K₂ H w₁ w₂ →
            ∀ a : G, a ∈ normalizer (H : Set G) → a ^ 3 = 1 → a⁻¹ * z * a = t →
              a⁻¹ * t * a = z * t →
                ∀ y ∈ H, (y ∈ K₁ ∨ y ∈ K₂) → y ∉ Subgroup.zpowers z → (orderOf y).Prime →
                  Odd (orderOf y) → a * y * a⁻¹ = y →
                    3 ^ (3 * n) ∣ Nat.card ↥(centralizer ({y} : Set G))

end CFSG.GH74.GLS.Stage4.Rest
