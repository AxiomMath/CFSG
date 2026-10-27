module

public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def FourSub {K : Type} [Group K] (S : Subgroup K) : Type :=
  {U : Subgroup K // U ≤ S ∧ Open.IsElemAbelian 2 U ∧ Nat.card U = 4}

@[expose] def FourAdj {K : Type} [Group K] (S : Subgroup K) (U V : FourSub S) : Prop :=
  ∃ E : Subgroup K, E ≤ S ∧ Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U.1 ≤ E ∧ V.1 ≤ E

structure CoverSylowData (n : ℕ) : Prop where
  card : ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n → ∀ S : Sylow 2 K,
    Nat.card S = if n ≤ 9 then 128 else 256
  rank : ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n → ∀ S : Sylow 2 K,
    Open.pRank 2 (S : Subgroup K) = 4
  four_in_E8 : ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n → ∀ S : Sylow 2 K,
    ∀ U : Subgroup K, U ≤ (S : Subgroup K) → Open.IsElemAbelian 2 U → Nat.card U = 4 →
      ∃ E : Subgroup K, E ≤ (S : Subgroup K) ∧ Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E
  connected : ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n → ∀ S : Sylow 2 K,
    ∀ U V : FourSub (S : Subgroup K), Relation.ReflTransGen (FourAdj (S : Subgroup K)) U V
  half_centralizer : ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n → ∀ S : Sylow 2 K,
    ∃ y ∈ (S : Subgroup K), orderOf y = 2 ∧ y ∉ center K ∧
      ((centralizer ({y} : Set K)).subgroupOf (S : Subgroup K)).index = 2

structure AlternatingBalanceData (n : ℕ) : Prop where
  no_odd : n ≤ 10 → ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n →
    ∀ X : Subgroup K, IsPGroup 2 X → Nat.card X = 2 ^ (if n ≤ 9 then 6 else 7) →
      ∀ P : Subgroup K, Odd (Nat.card P) → X ≤ normalizer (P : Set K) → P = ⊥
  no_odd' : ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n →
    ∀ X : Subgroup K, IsPGroup 2 X → Nat.card X = 2 ^ (if n ≤ 9 then 6 else 7) →
      ∀ P : Subgroup K, Nat.Coprime (Nat.card P) 6 → X ≤ normalizer (P : Set K) → P = ⊥
  one_class : ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n → ∀ u v : K,
    orderOf u = 2 → orderOf v = 2 → u ∉ center K → v ∉ center K → IsConj u v

abbrev CentQuot {G : Type} [Group G] (t : G) : Type :=
  ↥(centralizer ({t} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({t} : Set G))

end CFSG.OddStandard.Solomon75
