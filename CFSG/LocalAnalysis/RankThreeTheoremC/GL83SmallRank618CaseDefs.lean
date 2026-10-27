module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped MatrixGroups

structure Prop614Layer {G : Type} [Group G] [Finite G] (P : Sylow 3 G) (M H K : Subgroup G)
    (x z b : G) : Prop where
  mem : b ∈ zpowers x ⊔ zpowers z
  not_mem : b ∉ zpowers z
  centralizes : ⁅zpowers b, K⁆ ≤ rankThreePrimeCore 3 H
  caseOne : ∃ T : Subgroup G, SmallRankSylowTwo P M T ∧ SmallRankCaseOne b T
  kbar : ∃ f : ↥K →* PSL(3, ZMod 2), Function.Surjective f ∧
    ∀ k : ↥K, f k = 1 ↔ (k : G) ∈ rankThreePrimeCore 3 H
  layer : ∃ L : Subgroup G, L ≤ K ∧ L ≤ centralizer ({b} : Set G) ∧
    Nonempty (↥L ≃* PSL(3, ZMod 2)) ∧
    ∀ k ∈ K, ∃ l ∈ L, ∃ o ∈ rankThreePrimeCore 3 H, k = l * o
  fixed_point_free : ∀ o ∈ rankThreePrimeCore 3 H, b * o = o * b → o = 1

@[expose] def GL83SmallRankProp614Core19 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → Group.IsSolvable M →
    Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ H S : Subgroup G, Prop614Extremal M (zpowers x ⊔ zpowers z) H S →
        ¬ 3 ∣ (zpowers x ⊔ zpowers z).relIndex H →
        H = normalizer (pCoreOf 2 H : Set G) →
        IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S →
        pCoreOf 2 H ≤ S →
        (∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S →
          S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (S₀ : Set G) →
          normalizer (S₀ : Set G) ≤ M) →
        (∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
          normalizer (S₀ : Set G) ≤ M) →
        rankThreePrimeCore 3 H ≤ M →
        (∃ (K : Subgroup G) (b : G), Prop614Component M H K x z ∧
          Prop614Layer P M H K x z b) → False

end CFSG.LocalAnalysis.RankThreeTheoremC
