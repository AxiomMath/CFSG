module

public import CFSG.Foundations.Catalog
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

@[expose] def KFactSylowNormalizerIrreducible : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsKGroup K → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) →
    ∀ P : Subgroup K, IsElemAbelian 3 P → Nat.card P = 9 → ¬ 3 ∣ P.index →
      ∀ L : Subgroup K, L ≤ P → Nat.card L = 3 →
        ¬ normalizer (P : Set K) ≤ normalizer (L : Set K)

@[expose] def KFactOutThreePrimeSimple : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsKGroup K → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → (∃ P : Subgroup K, Nat.card P = 3 ∧ ¬ 3 ∣ P.index) →
    ∀ φ : MulAut K, (∃ n : ℕ, φ ^ (3 ^ n) = 1) → ∃ k : K, φ = MulAut.conj k

structure Data618 {Y : Type} [Group Y] [Finite Y] (B Z Y₀ : Subgroup Y) : Prop where
  kgroup : CFSG.IsKGroup Y
  core : ∀ N : Subgroup Y, N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥
  elem : IsElemAbelian 3 B
  card_B : Nat.card B = 9
  sylow : ¬ 3 ∣ B.index
  le_B : Z ≤ B
  card_Z : Nat.card Z = 3
  fix_Z : normalizer (B : Set Y) ≤ normalizer (Z : Set Y)
  cover : normalizer (Z : Set Y) ≤ Y₀
  proper : Y₀ ≠ ⊤

structure Prop614Component {G : Type} [Group G] [Finite G] (M H K : Subgroup G) (x z : G) :
    Prop where
  le : K ≤ H
  normal : H ≤ normalizer (K : Set G)
  not_le : ¬ K ≤ M
  mem : zpowers z ≤ K
  rank_one : CFSG.Open.pRank 3 K = 1
  perfect : ⁅K, K⁆ = K
  lt : K ⊓ rankThreePrimeCore 3 H < K
  maximal : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal →
    K ⊓ rankThreePrimeCore 3 H ≤ N → N = K ⊓ rankThreePrimeCore 3 H ∨ N = K
  centralizes : ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
    ⁅zpowers b, K⁆ ≤ rankThreePrimeCore 3 H

@[expose] def GL83SmallRankProp614Core18 (G : Type) [Group G] [Finite G] : Prop :=
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
        (∃ K : Subgroup G, Prop614Component M H K x z) → False

end CFSG.LocalAnalysis.RankThreeTheoremC
