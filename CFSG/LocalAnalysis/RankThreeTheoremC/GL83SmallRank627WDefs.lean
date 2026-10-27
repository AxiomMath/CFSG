module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

@[expose] def SmallRankCaseTwoW {G : Type} [Group G] [Finite G] (M : Subgroup G) (x : G)
    (T : Subgroup G) : Prop :=
  (∃ n : ℕ, rankThreeIsQ8CentralCyclic (T ⊓ centralizer ({x} : Set G)) n) ∧
    centralizer ({x} : Set G) ≤ (M ⊓ centralizer ({x} : Set G)) ⊔
      rankThreePrimeCore 2 (rankThreePrimeCore 3 (centralizer ({x} : Set G)))

@[expose] def GL83SmallRankProp627W (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
    p = 3 ∧ ∀ x : G, SmallRankPoint P M x → ∀ T : Subgroup G, SmallRankSylowTwo P M T →
      SmallRankCaseOne x T ∨ SmallRankCaseTwoW M x T

end CFSG.LocalAnalysis.RankThreeTheoremC
