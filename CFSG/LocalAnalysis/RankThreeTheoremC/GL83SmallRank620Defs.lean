module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Thompson
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

structure Data620 {G : Type} [Group G] [Finite G] (M B H S K : Subgroup G) (z b : G)
    (f : ↥K →* GL32) : Prop extends Data619 M B H S K z f where
  M_solvable : Group.IsSolvable M
  primeCore_le : ∀ N : Subgroup G, N ≤ H → H ≤ normalizer (N : Set G) →
    Nat.Coprime 3 (Nat.card N) → N ≤ pCoreOf 2 H
  B_card : Nat.card B = 9
  B_sylow : ¬ 3 ∣ B.relIndex H
  b_mem : b ∈ B
  b_order : orderOf b = 3
  b_not_mem : b ∉ zpowers z
  B_eq : B = zpowers z ⊔ zpowers b
  b_cent : ⁅zpowers b, K⁆ ≤ pCoreOf 2 H
  b_fpf : ∀ o ∈ pCoreOf 2 H, b * o = o * b → o = 1
  K_perfect : ⁅K, K⁆ = K
  S_le : S ≤ K ⊔ pCoreOf 2 H
  S_index : (pCoreOf 2 H).relIndex S = 4

@[expose] def FStarQuotientEq {G : Type} [Group G] (H N W : Subgroup G) : Prop :=
  ∃ hN : (N.subgroupOf H).Normal,
    letI := hN
    CFSG.Open.genFittingFStar (↥H ⧸ N.subgroupOf H) =
      (W.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))

@[expose] def CampbellFails {G : Type} [Group G] (H S K : Subgroup G) : Prop :=
  ∃ R : Subgroup G, S ≤ R ∧ R ≤ K ⊔ pCoreOf 2 H ∧ IsPGroup 2 R ∧
    ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index ∧
    ¬ ((K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter R : Subgroup G) : Set G) ≤
      normalizer (S : Set G))

@[expose] def KFactCampbell : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X K R P : Subgroup A),
    X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X →
    K ≤ X → X ≤ normalizer (K : Set A) → ⁅K, K⁆ = K → X = K ⊔ pCoreOf 2 X →
    (∃ f : ↥K →* GL32, Function.Surjective f ∧ ∀ k : ↥K, f k = 1 ↔ (k : A) ∈ pCoreOf 2 X) →
    R ≤ X → IsPGroup 2 R → ¬ 2 ∣ (R.subgroupOf X).index →
    R ≤ P → P ≤ X → (P.subgroupOf X).index = 7 →
    X ⊓ centralizer ((omegaCenter R : Subgroup A) : Set A) ≤ P →
    (∀ Q₀ : Subgroup A, Q₀ ≤ pCoreOf 2 P → Q₀ ≠ ⊥ →
      (Q₀.subgroupOf (pCoreOf 2 P)).Characteristic → ¬ X ≤ normalizer (Q₀ : Set A)) →
    ∃ A₀ B₀ : Subgroup A, A₀ ≤ B₀ ∧ B₀ ≤ omegaCenter (K ⊓ pCoreOf 2 X) ∧
      X ≤ normalizer (A₀ : Set A) ∧ X ≤ normalizer (B₀ : Set A) ∧
      K ≤ centralizer (A₀ : Set A) ∧
      (∀ w ∈ omegaCenter (K ⊓ pCoreOf 2 X), ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ B₀) ∧
      A₀.relIndex B₀ = 8 ∧
      ∀ g ∈ X, (∀ u ∈ B₀, g * u * g⁻¹ * u⁻¹ ∈ A₀) → g ∈ pCoreOf 2 X

@[expose] def GL83SmallRankProp614Core22 (G : Type) [Group G] [Finite G] : Prop :=
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
        rankThreePrimeCore 3 H ≤ pCoreOf 2 H →
        (∃ (K : Subgroup G) (b : G), Prop614Component M H K x z ∧
          Prop614Layer P M H K x z b ∧
          S ≤ K ⊔ pCoreOf 2 H ∧ (pCoreOf 2 H).relIndex S = 4 ∧
          FStarQuotientEq H (pCoreOf 2 H) (K ⊔ (zpowers x ⊔ zpowers z))) → False

@[expose] def GL83SmallRankProp614Core23 (G : Type) [Group G] [Finite G] : Prop :=
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
        rankThreePrimeCore 3 H ≤ pCoreOf 2 H →
        (∃ (K : Subgroup G) (b : G), Prop614Component M H K x z ∧
          Prop614Layer P M H K x z b ∧
          S ≤ K ⊔ pCoreOf 2 H ∧ (pCoreOf 2 H).relIndex S = 4 ∧
          FStarQuotientEq H (pCoreOf 2 H) (K ⊔ (zpowers x ⊔ zpowers z)) ∧
          CampbellFails H S K) → False

end CFSG.LocalAnalysis.RankThreeTheoremC
