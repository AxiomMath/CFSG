module

public import CFSG.GH74.GLS.Types

public section

namespace CFSG.GH74.E2

open Subgroup

structure Hyp (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  twoRank : 3 ≤ Open.twoRank G
  gen4 : Gen4 G
  kgh : KGH G
  sylow_nonabelian : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)
  layer : ∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥
  restrictedEven : GLS.IsRestrictedEvenType G

@[expose] def ElemAb {G : Type*} [Group G] (p : ℕ) (A : Subgroup G) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ p = 1

@[expose] def CaseI {G : Type*} [Group G] (t : G) (A : Subgroup G) : Prop :=
  orderOf t = 2 ∧ A ≤ centralizer ({t} : Set G) ∧ ElemAb 3 A ∧ Nat.card A = 27

structure CaseII {G : Type*} [Group G] (t t' a : G) (A B : Subgroup G) : Prop where
  order_t : orderOf t = 2
  order_t' : orderOf t' = 2
  ne : t ≠ t'
  comm : t * t' = t' * t
  order_a : orderOf a = 3
  conj_t : a * t * a⁻¹ = t'
  conj_t' : a * t' * a⁻¹ = t * t'
  elemAb : ElemAb 3 A
  card_A : Nat.card A = 27
  a_mem : a ∈ A
  B_le : B ≤ A
  card_B : Nat.card B = 9
  centralizes_t : ∀ b ∈ B, b * t = t * b
  centralizes_t' : ∀ b ∈ B, b * t' = t' * b
  free : ∀ u : G, orderOf u = 2 → ¬ A ≤ centralizer ({u} : Set G)

@[expose] def NoOddRankFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ t : G, orderOf t = 2 → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ B : Subgroup G, B ≤ centralizer ({t} : Set G) → ElemAb p B → Nat.card B ≤ p

@[expose] def NoCaseI : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t : G) (A : Subgroup G), ¬ CaseI t A

@[expose] def NoCaseII : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B : Subgroup G), ¬ CaseII t t' a A B

end CFSG.GH74.E2
