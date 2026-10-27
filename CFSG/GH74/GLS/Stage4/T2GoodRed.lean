module

public import CFSG.GH74.GLS.Stage4.RestCases
public import CFSG.GH74.GLS.Stage4.T6Basic

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank

@[expose] def Ch6P71Out {G : Type} [Group G] (n : ℕ) (z : G) (K K' : Subgroup G) : Prop :=
  ∀ (N : T2N3 G) (u : G), N.z = z → N.K₁ = K → N.K₂ = K' → N.q₁ = 3 ^ n → N.q₂ = 3 ^ n →
    Ch6Coord N.toT2N2.toT2N1 → Ch6Sec5 N u →
      Nat.card ↥(T6.R₂ N 3) = N.q₁ ^ 2 * N.q₂ ^ 3 ∧
        ∃ P₀ : Subgroup G, P₀ ≤ N.F ∧ IsPGroup 3 ↥P₀ ∧
          ∃ T : Sylow 3 G, (T : Subgroup G) = (T6.R₂ N 3 ⊔ N.X₁) ⊔ P₀

@[expose] def Ch6T2Prop71 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 2 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
      ¬ Ch6Bad3 G →
        ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
          Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
            Ch6P71Out n z K₁ K₂ ∨ Ch6P71Out n z K₂ K₁

end CFSG.GH74.GLS.Stage4.Rest
