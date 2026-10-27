module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PrimeInduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped MatrixGroups

structure SmallRankSituation (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M : Subgroup G) : Prop where
  mem_sigmaA : p ∈ rankThreeSigmaA G
  isCoreMaxLocal : IsCoreMaxLocal p P M
  gamma_two_le : rankThreeGamma 2 p (P : Subgroup G) ≤ M
  not_gamma_one_le : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M
  largeObstruction_empty : ∀ y : G, ¬ IsLargeObstruction p M y
  largerPrimesUnique : LargerPrimesUnique G p
  not_uniquenessAt : ¬ UniquenessAt G p P M

structure SmallRankPoint {G : Type} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (M : Subgroup G) (x : G) : Prop where
  mem : x ∈ (P : Subgroup G)
  ne_one : x ≠ 1
  pow_eq_one : x ^ p = 1
  not_centralizer_le : ¬ centralizer ({x} : Set G) ≤ M
  sylow_centralizer : ¬ p ∣ (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
    (centralizer ({x} : Set G))).index

structure SmallRankCentral {G : Type} [Group G] [Finite G] {p : ℕ} (P : Sylow p G) (z : G) :
    Prop where
  mem : z ∈ (P : Subgroup G)
  centralizes : z ∈ centralizer ((P : Subgroup G) : Set G)
  ne_one : z ≠ 1
  pow_eq_one : z ^ p = 1

structure SmallRankSylowTwo {G : Type} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (M : Subgroup G) (T : Subgroup G) : Prop where
  le_core : T ≤ rankThreePrimeCore p M
  isPGroup : IsPGroup 2 T
  index_odd : ¬ 2 ∣ (T.subgroupOf (rankThreePrimeCore p M)).index
  normalized : (P : Subgroup G) ≤ normalizer (T : Set G)

@[expose] def SmallRankCaseOne {G : Type} [Group G] (x : G) (T : Subgroup G) : Prop :=
  Nonempty ((T ⊓ centralizer ({x} : Set G) : Subgroup G) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∧
    (Nonempty (centralizer ({x} : Set G) ≃* (Multiplicative (ZMod 3) × PSL(3, ZMod 2))) ∨
      Nonempty (centralizer ({x} : Set G) ≃*
        (Multiplicative (ZMod 3) × MulAut PSL(3, ZMod 2))))

@[expose] def SmallRankCaseTwo {G : Type} [Group G] [Finite G] (M : Subgroup G) (x : G)
    (T : Subgroup G) : Prop :=
  (∃ n : ℕ, rankThreeIsQ8CentralCyclic (T ⊓ centralizer ({x} : Set G)) n) ∧
    centralizer ({x} : Set G) ≤ (M ⊓ centralizer ({x} : Set G)) ⊔
      rankThreePrimeCore 2 (rankThreePrimeCore 3 (centralizer ({x} : Set G))) ∧
    CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (rankThreePrimeCore 3
      (centralizer ({x} : Set G)))) ⊓ M = ⊥

@[expose] def GL83SmallRankProp627 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
    p = 3 ∧ ∀ x : G, SmallRankPoint P M x → ∀ T : Subgroup G, SmallRankSylowTwo P M T →
      SmallRankCaseOne x T ∨ SmallRankCaseTwo M x T

@[expose] def GL83SmallRankProp614 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ H : Subgroup G, IsTwoLocal H → zpowers x ⊔ zpowers z ≤ H →
        (∃ S : Subgroup G, S ≤ H ⊓ M ∧ IsPGroup 2 S ∧ S ≠ ⊥ ∧
          zpowers x ⊔ zpowers z ≤ normalizer (S : Set G)) → H ≤ M

@[expose] def GL83SmallRankProp632 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M →
    Group.IsSolvable M ∧
      Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))

theorem GL83SmallRankProp627.eq_three {G : Type} [Group G] [Finite G]
    (h : GL83SmallRankProp627 G) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hs : SmallRankSituation G p P M) : p = 3 :=
  (h p P M hs).1

end CFSG.LocalAnalysis.RankThreeTheoremC
