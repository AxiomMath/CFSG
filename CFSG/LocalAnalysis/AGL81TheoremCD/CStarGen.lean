module

public import CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD

open CFSG.Open Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def sigmaSet (G : Type) [Group G] [Finite G] (N : Subgroup G) : Set ℕ :=
  {q | q ∈ rankThreeSigmaA G ∧ 2 ≤ CFSG.Open.pRank q N}

@[expose] def AlmostClauseTwoCore (N P : Subgroup G) (p : ℕ) : Prop :=
  5 ≤ p ∧ Group.IsSolvable N ∧
    ∃ P₀ : Subgroup G, P₀ ≤ P ∧ Nat.card P₀ = p ∧
      (∀ g : G, rankThreeConj g P₀ ≤ P → rankThreeConj g P₀ = P₀) ∧
      (∃ (_ : Fact p.Prime) (m : ℕ), 2 ≤ m ∧
        Nonempty (rankThreeLayer (centralizer (P₀ : Set G)) ≃* PSL(2, GaloisField p m))) ∧
      ¬ rankThreeLayer (centralizer (P₀ : Set G)) ≤ N ∧
      (∀ Y : Subgroup G, Y ≤ P → Nat.card Y = p → Y ≠ P₀ → normalizer (Y : Set G) ≤ N) ∧
      (∀ q : ℕ, q.Prime → q ≠ 2 → pRank q (rankThreePrimeCore p N) ≤ 1) ∧
      ∀ q : ℕ, q.Prime → q ≠ 2 →
        pRank q (centralizer (P₀ : Set G) ⊓
          centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G)) ≤ 1

@[expose] def AlmostStrongCore (N : Subgroup G) (p : ℕ) : Prop :=
  ∃ P : Sylow p G, (P : Subgroup G) ≤ N ∧ rankThreeGamma 2 p (P : Subgroup G) ≤ N ∧
    (rankThreeGamma 1 p (P : Subgroup G) ≤ N ∨ AlmostClauseTwoCore N (P : Subgroup G) p ∨
      (p = 3 ∧ rankThreeClauseC N (P : Subgroup G)))

structure CStarGen (G : Type) [Group G] [Finite G] : Prop extends StandingGen G where
  embed : ∀ p ∈ rankThreeSigmaA G, ∀ N : Subgroup G, rankThreeIsMaxTwoLocal N →
    ∀ Q : Subgroup G, Q ≤ N → IsPGroup p Q → 2 ≤ pRank p Q →
      ∀ H : Subgroup G, IsTwoLocal H → Q ≤ H → H ≤ N
  exists_maxLocal : ∀ p ∈ rankThreeSigmaA G,
    ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ p ∈ sigmaSet G N
  almost : ∀ N : Subgroup G, rankThreeIsMaxTwoLocal N → ∀ p ∈ sigmaSet G N,
    AlmostStrongCore N p
  off_sigma : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ rankThreeSigmaA G →
    rankThreeLocalRank p G ≤ 3 ∧
      (rankThreeLocalRank p G = 3 → 4 ≤ evenRank G ∨ p ≤ 5)

end CFSG.LocalAnalysis.AGL81TheoremCD
