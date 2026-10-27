module

public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Foundations.Basic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.Open
open scoped MatrixGroups

@[expose] def GmiCatFourInput : Prop :=
  ∀ (L : Type) [Group L] [Finite L], goldschmidtSimpleType L → 4 ∣ Nat.card L

@[expose] def GmiCatSimpleInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K T : Subgroup Y), IsSylowOf 2 T K →
    (∀ n : ℕ, 2 ≤ n → Nonempty (K ≃* PSL(2, GaloisField 2 n)) →
      Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1) ∧ Nat.card T = 2 ^ n ∧ ∀ x ∈ T, x ^ 2 = 1) ∧
    (∀ n : ℕ, 1 ≤ n → Nonempty (K ≃* Sz n) → ¬ 3 ∣ Nat.card K) ∧
    (∀ n : ℕ, 2 ≤ n → Nonempty (K ≃* PSU3 2 n) → Nat.card T = (2 ^ n) ^ 3 ∧
      ∀ W : Subgroup Y, W ≤ T → (∀ x ∈ W, x ^ 2 = 1) → Nat.card W ≤ 2 ^ n) ∧
    (∀ (p n : ℕ) [Fact p.Prime], Odd p → 0 < n → (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) →
      Nonempty (K ≃* PSL(2, GaloisField p n)) → Nat.card T = 4 ∧ ∀ x ∈ T, x ^ 2 = 1) ∧
    (Nonempty (K ≃* goldschmidtJ1) → Nat.card K = 175560 ∧ ∀ x ∈ T, x ^ 2 = 1)

@[expose] def GmiCatSchurInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), CFSG.IsQuasisimple K →
    IsPGroup 2 (center K) → center K ≠ ⊥ →
    (∀ n : ℕ, 3 ≤ n → IsEmpty ((K ⧸ center K) ≃* PSL(2, GaloisField 2 n))) ∧
    (∀ n : ℕ, 2 ≤ n → IsEmpty ((K ⧸ center K) ≃* PSU3 2 n)) ∧
    IsEmpty ((K ⧸ center K) ≃* goldschmidtJ1) ∧
    ∀ (p n : ℕ) [Fact p.Prime], Odd p → 0 < n → (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) →
      Nonempty ((K ⧸ center K) ≃* PSL(2, GaloisField p n)) →
      ∀ T : Subgroup Y, IsSylowOf 2 T K → ∃ u ∈ K, (∀ x ∈ T, u * x * u⁻¹ ∈ T) ∧
        ∀ k ∈ T, (∃ y ∈ K, k * y ≠ y * k) → k * (u * k * u⁻¹) ≠ u * k * u⁻¹ * k

end CFSG.SeitzReduction.RankOne
