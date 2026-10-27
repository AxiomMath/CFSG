module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixDefs
public import CFSG.GH74.GLS.Stage4.RestSetup

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

structure Ch6MixTSdata {G : Type} [Group G] (N : T2N3 G) (p : ℕ) (y : G) (R : Subgroup G) : Prop where
  yK : y ∈ N.K₁
  y_ne : y ∉ Subgroup.zpowers N.z
  y_prime : (orderOf y).Prime
  y_odd : Odd (orderOf y)
  y_dvd : orderOf y ∣ N.q₁ + 1
  R_p : IsPGroup p ↥R
  X_le : N.X₂ ≤ R
  R_cent : R ≤ Subgroup.centralizer (N.X₂ : Set G)
  R_card : Nat.card ↥R = N.q₂ ^ 3
  R_center : ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ N.X₂
  X_comm : N.X₂ ≤ ⁅R, R⁆
  R_comm : ∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ N.X₂
  R_inv : ∀ r ∈ R, N.z * r * N.z⁻¹ * r ∈ N.X₂
  R_exp : ∀ r ∈ R, r ^ p ∈ N.X₂
  y_cent : ∀ r ∈ R, y * r = r * y

@[expose] def Ch6MixSecEx : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁]
      [Field F₂] (t : G), Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
        q₂ < q₁ → q₁ % 4 ≠ q₂ % 4 →
          ∃ (N : T2N3 G) (u : G), N.z = z ∧ N.K₁ = K₁ ∧ N.K₂ = K₂ ∧ N.q₁ = q₁ ∧ N.q₂ = q₂ ∧
            Ch6Sec5M N u ∧ Ch6Coord2 N.toT2N2.toT2N1

@[expose] def Ch6MixTS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ → q₂ < q₁ → q₁ % 4 ≠ q₂ % 4 →
      ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
        Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
          ∀ (p n : ℕ), p.Prime → p ≠ 2 → q₂ = p ^ n →
            ∀ (N : T2N3 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
              Ch6Coord2 N.toT2N2.toT2N1 → Ch6Sec5M N u →
                ∃ (y : G) (R : Subgroup G), Ch6MixTSdata N p y R

end CFSG.GH74.GLS.Stage4.Rest
