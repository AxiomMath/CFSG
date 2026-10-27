module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

structure GL83SmallRankInterface (G : Type) [Group G] [Finite G] : Prop where
  prop614 : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G),
    Prop627Failure G p P M x z T → ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M
  prop65 : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G),
    Prop627Failure G p P M x z T → SmallRankCover p M x →
      (p = 3 ∨ p = 5) → (p = 3 → Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2)) →
      (p = 5 → smallRankIsQ8D8 (smallRankR x z T)) → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
        pCoreOf q (smallRankD p x) ⊓ M ≠ ⊥ →
          normalizer ((pCoreOf q (smallRankD p x) ⊓ M : Subgroup G) : Set G) ≤ M

@[expose] def SmallRankInvolutionRankLE {K : Type} [Group K] [Finite K] (f r : ℕ)
    (S X : Subgroup K) : Prop :=
  ∀ y ∈ S, y ^ 2 = 1 → y ≠ 1 → CFSG.Open.pRank f (X ⊓ centralizer ({y} : Set K)) ≤ r

@[expose] def KFactZAction628 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f : ℕ), p.Prime → f.Prime → p ≠ 2 → f ≠ 2 → f ≠ p →
    ∀ (S X N : Subgroup K) (z : K), IsPGroup 2 S → IsPGroup f X → N ≤ X →
      (N.subgroupOf X).Normal → ¬ X ≤ N → z ^ p = 1 → z ≠ 1 →
      zpowers z ≤ normalizer (S : Set K) → S ⊔ zpowers z ≤ normalizer (X : Set K) →
      S ⊔ zpowers z ≤ normalizer (N : Set K) → ⁅zpowers z, S⁆ ≠ ⊥ →
      (∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
        X ⊓ centralizer (S₀ : Set K) ≤ N) →
      X ⊓ centralizer ({z} : Set K) ≤ N →
      SmallRankInvolutionRankLE f 3 S X →
      (p = 3 → SmallRankInvolutionRankLE f 2 S X) →
        (p = 3 ∨ p = 5) ∧ (p = 3 → Nonempty (↥⁅zpowers z, S⁆ ≃* QuaternionGroup 2)) ∧
          (p = 5 → smallRankIsQ8D8 ⁅zpowers z, S⁆)

@[expose] def KFactZAction629 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f : ℕ), p.Prime → f.Prime → p ≠ 2 → f ≠ 2 → f ≠ p →
    (p = 3 ∨ p = 5) → ∀ (S F : Subgroup K) (z : K), IsPGroup 2 S → IsElemAbelian f F → F ≠ ⊥ →
      z ^ p = 1 → z ≠ 1 → zpowers z ≤ normalizer (S : Set K) →
      S ⊔ zpowers z ≤ normalizer (F : Set K) →
      (p = 3 → Nonempty (↥⁅zpowers z, S⁆ ≃* QuaternionGroup 2)) →
      (p = 5 → smallRankIsQ8D8 ⁅zpowers z, S⁆) →
      (∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
        F ⊓ centralizer (S₀ : Set K) = ⊥) →
      F ⊓ centralizer ({z} : Set K) = ⊥ →
      SmallRankInvolutionRankLE f 3 S F →
      (p = 3 → SmallRankInvolutionRankLE f 2 S F) →
      ¬ (p = 3 ∧ ∃ n : ℕ, rankThreeIsQ8CentralCyclic S n) →
        (Nat.card F = f ^ 4 ∧ ∀ y ∈ smallRankCenter ⁅zpowers z, S⁆, y ≠ 1 → ∀ a ∈ F,
          y * a * y⁻¹ = a⁻¹) ∧
        ((p = 5 → ∃ n : ℕ, smallRankIsQ8D8CentralCyclic S n) ∧
          (p = 3 → ∃ n : ℕ, smallRankIsQ8Quaternion S n) ∧
          smallRankCenter ⁅zpowers z, S⁆ = smallRankOmega 2 (smallRankCenter S)) ∧
        (∀ A : Subgroup K, A ≤ S → zpowers z ≤ normalizer (A : Set K) → ⁅A, zpowers z⁆ ≠ ⊥ →
          ⁅zpowers z, S⁆ ≤ A)

end CFSG.LocalAnalysis.RankThreeTheoremC
