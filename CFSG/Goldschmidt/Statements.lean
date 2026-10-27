module

public import CFSG.Goldschmidt.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)

@[expose] def S_N1 : Prop :=
  ∀ n : ℕ, IH n → ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → TopFor X ∧ GoldFor X

@[expose] def S_N11a : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], goldschmidtSimpleType K →
    ∀ T : Sylow 2 K, IsMulCommutative (Omega1 (T : Subgroup K)) →
    (IsMulCommutative (T : Subgroup K) → ∀ t ∈ (T : Subgroup K), t ^ 2 = 1) ∧
    (¬ IsMulCommutative (T : Subgroup K) →
      (∃ n : ℕ, 1 ≤ n ∧ Nonempty (K ≃* Sz n)) ∨ (∃ f : ℕ, 2 ≤ f ∧ Nonempty (K ≃* PSU3 2 f)))

@[expose] def S_N11b : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], goldschmidtSimpleType K →
    ∀ T : Sylow 2 K, IsMulCommutative (Omega1 (T : Subgroup K)) →
    4 ≤ Nat.card (Omega1 (T : Subgroup K)) ∧
    ∀ x ∈ Omega1 (T : Subgroup K), ∀ y ∈ Omega1 (T : Subgroup K), x ≠ 1 → y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((Omega1 (T : Subgroup K) : Subgroup K) : Set K),
        n⁻¹ * x * n = y

@[expose] def S_N11c : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    ((∃ n : ℕ, 1 ≤ n ∧ Nonempty (K ≃* Sz n)) ∨ (∃ f : ℕ, 2 ≤ f ∧ Nonempty (K ≃* PSU3 2 f))) →
    ∀ T : Sylow 2 K, Omega1 (T : Subgroup K) = sylowCenter (T : Subgroup K) ∧
      ⁅(T : Subgroup K), (T : Subgroup K)⁆ ≤ sylowCenter (T : Subgroup K)

@[expose] def S_N13 : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    ((∃ n : ℕ, 1 ≤ n ∧ Nonempty (K ≃* Sz n)) ∨ (∃ f : ℕ, 2 ≤ f ∧ Nonempty (K ≃* PSU3 2 f))) →
    ∀ (T : Sylow 2 K) (β : K → K → ZMod 2),
    (∀ x ∈ (T : Subgroup K), ∀ x' ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K),
      β (x * x') y = β x y + β x' y) →
    (∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), ∀ y' ∈ (T : Subgroup K),
      β x (y * y') = β x y + β x y') →
    (∀ z ∈ sylowCenter (T : Subgroup K), ∀ y ∈ (T : Subgroup K), β z y = 0) →
    (∀ x ∈ (T : Subgroup K), ∀ z ∈ sylowCenter (T : Subgroup K), β x z = 0) →
    (∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ x ∈ (T : Subgroup K),
      ∀ y ∈ (T : Subgroup K), β (n⁻¹ * x * n) (n⁻¹ * y * n) = β x y) →
    ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), β x y = 0

@[expose] def S_N15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ (p ^ f % 8 = 1 ∨ p ^ f % 8 = 7) ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f) ∨
      Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (G ≃* CFSG.Assembly.LowTwoRank.StatedM11)) →
    (∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
    ∀ S : Sylow 2 G, ¬ IsMulCommutative (Omega1 (S : Subgroup G))

end CFSG.Goldschmidt
