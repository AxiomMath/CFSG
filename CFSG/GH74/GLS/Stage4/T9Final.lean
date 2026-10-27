module

public import CFSG.GH74.GLS.Stage4.T9Inequiv

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank

theorem ch6T2Sec9'_proved :
    ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
      ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
        ¬ (q₁ = 9 ∧ q₂ = 9) → (¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n) →
          ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
            Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
              ∀ (N : T2N4 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
                Ch6NumD N.p q₁ q₂ → Ch6Coord N.toT2N3.toT2N2.toT2N1 → Ch6Sec5 N.toT2N3 u →
                  Ch6S6 N.toCh6 → Ch6Shape N.toCh6 := by
  intro G _ _ _ _ Gs _ q₁ q₂ _ _ _ z K₁ K₂ F₁ F₂ _ _ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hNum hCoord
    hSec₅ hS6
  have h : T6.T6Ctx N.toT2N3 u N.p :=
    T6.t6Ctx_of hSet hRem (N := N.toT2N3) (u := u) (p := N.p) hz hK₁ hK₂ hq₁ hq₂ hNum hCoord hSec₅
  exact T9.t9_shape h hS6

end CFSG.GH74.GLS.Stage4.Rest

