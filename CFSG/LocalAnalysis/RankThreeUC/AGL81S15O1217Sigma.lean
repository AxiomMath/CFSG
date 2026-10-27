module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open scoped Pointwise

@[expose] def O1217Sigma : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      ∀ q p : ℕ, q ∈ sigmaM G M → p.Prime → p ≠ 2 →
        ∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ 2 →
          q ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E : Set G)) →
          (∀ A : Subgroup G, A ≤ E → Nat.card A = p →
            2 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (A : Set G))) →
          rankThreeGamma 1 p E ≤ M

@[expose] def O1219Sigma : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      ∀ q p : ℕ, q ∈ sigmaM G M → p.Prime → p ≠ 2 → p ∉ sigmaM G M →
        ∀ D : Subgroup G, D ≤ M → ¬ IsCyclic ↥D → (∀ x ∈ D, x ^ p = 1) → ⁅⁅D, D⁆, D⁆ = ⊥ →
          CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (D : Set G)) = CFSG.Open.pRank q M →
          ∃ E : Subgroup G, E ≤ D ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
            rankThreeGamma 1 p E ≤ M

theorem O1217.of_sigma (h : O1217Sigma) : O1217 :=
  fun G _ _ hS hUC M hM hw hst q p hq _ hp hp2 E hEM hE hEc hqC hrk =>
    h G hS hUC M hM hw hst q p hq hp hp2 E hEM hE hEc hqC hrk

end CFSG.LocalAnalysis.RankThreeUC.S15
