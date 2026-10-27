module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627WDefs
public import CFSG.Open.GorensteinWalterLBalanceMilestoneDefs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

section Objects

variable {G : Type} [Group G]

@[expose] def smallRankB (x z : G) : Subgroup G := zpowers x ⊔ zpowers z

@[expose] def smallRankS (x : G) (T : Subgroup G) : Subgroup G :=
  T ⊓ centralizer ({x} : Set G)

@[expose] def smallRankR (x z : G) (T : Subgroup G) : Subgroup G :=
  ⁅zpowers z, smallRankS x T⁆

@[expose] def smallRankD (p : ℕ) (x : G) : Subgroup G :=
  rankThreePrimeCore p (centralizer ({x} : Set G))

@[expose] def smallRankCenter (H : Subgroup G) : Subgroup G := H ⊓ centralizer (H : Set G)

@[expose] def smallRankOmega (p : ℕ) (A : Subgroup G) : Subgroup G :=
  closure {a : G | a ∈ A ∧ a ^ p = 1}

@[expose] def smallRankF (p f : ℕ) (x : G) : Subgroup G :=
  smallRankOmega f (smallRankCenter (pCoreOf f (smallRankD p x)))

@[expose] def smallRankIsQ8D8 (H : Subgroup G) : Prop :=
  ∃ A B : Subgroup G, Nonempty (A ≃* QuaternionGroup 2) ∧ Nonempty (B ≃* DihedralGroup 4) ∧
    (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ A ⊔ B = H ∧ Nat.card (A ⊓ B : Subgroup G) = 2

@[expose] def smallRankIsQ8D8CentralCyclic (H : Subgroup G) (n : ℕ) : Prop :=
  ∃ A B C : Subgroup G, Nonempty (A ≃* QuaternionGroup 2) ∧ Nonempty (B ≃* DihedralGroup 4) ∧
    IsCyclic C ∧ Nat.card C = 2 ^ n ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧
    (∀ a ∈ A, ∀ c ∈ C, a * c = c * a) ∧ (∀ b ∈ B, ∀ c ∈ C, b * c = c * b) ∧
    Nat.card (A ⊓ B : Subgroup G) = 2 ∧ Nat.card ((A ⊔ B) ⊓ C : Subgroup G) = 2 ∧
    A ⊔ B ⊔ C = H

@[expose] def smallRankIsQ8Quaternion (H : Subgroup G) (n : ℕ) : Prop :=
  ∃ A B : Subgroup G, Nonempty (A ≃* QuaternionGroup 2) ∧ 3 ≤ n ∧
    Nonempty (B ≃* QuaternionGroup (2 ^ (n - 2))) ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧
    A ⊔ B = H ∧ Nat.card (A ⊓ B : Subgroup G) = 2

@[expose] def SmallRankCover (p : ℕ) (M : Subgroup G) (x : G) : Prop :=
  centralizer ({x} : Set G) ≤ (M ⊓ centralizer ({x} : Set G)) ⊔
    rankThreePrimeCore 2 (rankThreePrimeCore p (centralizer ({x} : Set G)))

end Objects

variable {G : Type} [Group G] [Finite G]

structure Prop627Failure (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M : Subgroup G) (x z : G) (T : Subgroup G) : Prop where
  situation : SmallRankSituation G p P M
  point : SmallRankPoint P M x
  central : SmallRankCentral P z
  sylowTwo : SmallRankSylowTwo P M T
  fails : ¬ (p = 3 ∧ (SmallRankCaseOne x T ∨ SmallRankCaseTwoW M x T))

@[expose] def GL83SmallRankProp622 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
    ∀ x : G, SmallRankPoint P M x → ∀ T : Subgroup G, SmallRankSylowTwo P M T →
      SmallRankCover p M x ∨ (p = 3 ∧ SmallRankCaseOne x T)

@[expose] def Lemma628Concl (p : ℕ) (M : Subgroup G) (x z : G) (T : Subgroup G) : Prop :=
  (p = 3 ∨ p = 5) ∧
    (p = 3 → Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2)) ∧
    (p = 5 → smallRankIsQ8D8 (smallRankR x z T)) ∧
    CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD p x)) ⊓ M = ⊥

@[expose] def Lemma629Concl (p : ℕ) (M : Subgroup G) (x z : G) (T : Subgroup G) (f : ℕ) : Prop :=
  ((p = 5 → ∃ n : ℕ, smallRankIsQ8D8CentralCyclic (smallRankS x T) n) ∧
      (p = 3 → ∃ n : ℕ, smallRankIsQ8Quaternion (smallRankS x T) n) ∧
      smallRankCenter (smallRankR x z T) = smallRankOmega 2 (smallRankCenter (smallRankS x T))) ∧
    smallRankR x z T ≤ pCoreOf 2 M ∧
    rankThreeLocalRank f G ≤ 3 ∧
    (IsElemAbelian f (smallRankF p f x) ∧ Nat.card (smallRankF p f x) = f ^ 4 ∧
      ∀ y ∈ smallRankCenter (smallRankR x z T), y ≠ 1 → ∀ a ∈ smallRankF p f x,
        y * a * y⁻¹ = a⁻¹)

@[expose] def Lemma630Concl (p : ℕ) (x z : G) (T : Subgroup G) (f : ℕ) : Prop :=
  (∃ E : Subgroup G, E ≤ centralizer (smallRankF p f x : Set G) ∧ IsPGroup f E ∧
      ¬ f ∣ (E.subgroupOf (centralizer (smallRankF p f x : Set G))).index ∧
      smallRankS x T ⊔ smallRankB x z ≤ normalizer (E : Set G) ∧
      IsMulCommutative E ∧ CFSG.Open.pRank f E = 4 ∧ ¬ f ∣ E.index) ∧
    ∀ a ∈ smallRankF p f x, a ≠ 1 →
      ∀ g ∈ normalizer (smallRankF p f x : Set G) ⊓ centralizer ({a} : Set G),
        ∃ n : ℕ, g ^ (2 ^ n) ∈ centralizer (smallRankF p f x : Set G)

@[expose] def Lemma631Concl (p : ℕ) (f : ℕ) (x : G) : Prop :=
  ∃ a ∈ smallRankF p f x, a ≠ 1 ∧ ∃ J : Subgroup G,
    lBalanceIsPComponent f (centralizer ({a} : Set G)) J ∧ CFSG.Open.pRank f J = 3 ∧
      CFSG.Open.pRank f (smallRankF p f x ⊓ J) = 3

@[expose] def GL83SmallRankLemma628 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G),
    Prop627Failure G p P M x z T → SmallRankCover p M x → Lemma628Concl p M x z T

@[expose] def GL83SmallRankLemma629 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G),
    Prop627Failure G p P M x z T → SmallRankCover p M x → Lemma628Concl p M x z T →
      ∀ f : ℕ, f.Prime → f ≠ 2 → pCoreOf f (smallRankD p x) ≠ ⊥ → Lemma629Concl p M x z T f

@[expose] def GL83SmallRankLemma630 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G),
    Prop627Failure G p P M x z T → SmallRankCover p M x → Lemma628Concl p M x z T →
      ∀ f : ℕ, f.Prime → f ≠ 2 → pCoreOf f (smallRankD p x) ≠ ⊥ →
        Lemma629Concl p M x z T f → Lemma630Concl p x z T f

@[expose] def GL83SmallRankLemma631 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G),
    Prop627Failure G p P M x z T → SmallRankCover p M x → Lemma628Concl p M x z T →
      ∀ f : ℕ, f.Prime → f ≠ 2 → pCoreOf f (smallRankD p x) ≠ ⊥ →
        Lemma629Concl p M x z T f → Lemma630Concl p x z T f → Lemma631Concl p f x

@[expose] def KFactAbelianSylowRankThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsKGroup K → CFSG.Open.IsQuasisimple K →
    ∀ (f : ℕ), f.Prime → f ≠ 2 → ∀ P A : Subgroup K, IsPGroup f P → ¬ f ∣ P.index →
      IsMulCommutative P → A ≤ P → Nat.card A = f ^ 3 → (∀ y ∈ A, y ^ f = 1) →
      (∀ y ∈ P, y ^ f = 1 → y ∈ A) →
        ∃ g ∈ normalizer (P : Set K), ∀ n : ℕ, ∃ a ∈ A, g ^ (2 ^ n) * a ≠ a * g ^ (2 ^ n)

end CFSG.LocalAnalysis.RankThreeTheoremC
