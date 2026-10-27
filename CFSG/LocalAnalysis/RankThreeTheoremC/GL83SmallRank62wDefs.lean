module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

@[expose] def SmallRankNice {G : Type} [Group G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) :
    Prop :=
  p = 3 ∧ Group.IsSolvable M ∧
    Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))

structure GL83SmallRankInterfaceW (G : Type) [Group G] [Finite G] : Prop where
  prop614 : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G),
    Prop627Failure G p P M x z T → ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M
  fitting628 : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G),
    Prop627Failure G p P M x z T → SmallRankCover p M x → (p = 3 ∨ p = 5) →
      (p = 3 → Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2)) →
      (p = 5 → smallRankIsQ8D8 (smallRankR x z T)) → ¬ SmallRankNice p P M →
        CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD p x)) ⊓ M = ⊥

structure Lemma630Hyp (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (x z : G) (T : Subgroup G) (f : ℕ) : Prop where
  failure : Prop627Failure G p P M x z T
  cover : SmallRankCover p M x
  lemma628 : Lemma628Concl p M x z T
  prime : f.Prime
  ne_two : f ≠ 2
  core_ne_bot : pCoreOf f (smallRankD p x) ≠ ⊥
  lemma629 : Lemma629Concl p M x z T f

@[expose] def SmallRankSBSylow {G : Type} [Group G] (p f : ℕ) (x z : G) (T E : Subgroup G) :
    Prop :=
  E ≤ centralizer (smallRankF p f x : Set G) ∧ IsPGroup f E ∧
    ¬ f ∣ (E.subgroupOf (centralizer (smallRankF p f x : Set G))).index ∧
    smallRankS x T ⊔ smallRankB x z ≤ normalizer (E : Set G)

@[expose] def Lemma630Iii {G : Type} [Group G] (p f : ℕ) (x : G) : Prop :=
  ∀ a ∈ smallRankF p f x, a ≠ 1 →
    ∀ g ∈ normalizer (smallRankF p f x : Set G) ⊓ centralizer ({a} : Set G),
      ∃ n : ℕ, g ^ (2 ^ n) ∈ centralizer (smallRankF p f x : Set G)

structure GL83SmallRankLemma630Core (G : Type) [Group G] [Finite G] : Prop where
  exists_sylow : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G) (f : ℕ),
    Lemma630Hyp G p P M x z T f → ∃ E : Subgroup G, SmallRankSBSylow p f x z T E
  evasion : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G) (f : ℕ),
    Lemma630Hyp G p P M x z T f → ¬ SmallRankNice p P M →
      ∀ E : Subgroup G, SmallRankSBSylow p f x z T E → E ⊓ M = ⊥
  iii : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G) (f : ℕ),
    Lemma630Hyp G p P M x z T f → Lemma630Iii p f x

end CFSG.LocalAnalysis.RankThreeTheoremC
