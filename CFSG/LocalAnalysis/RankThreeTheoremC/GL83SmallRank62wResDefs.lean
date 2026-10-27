module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

structure GL83SmallRankLemma630Res (G : Type) [Group G] [Finite G] : Prop where
  evasion : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G) (f : ℕ),
    Lemma630Hyp G p P M x z T f → ¬ SmallRankNice p P M →
      ∀ E : Subgroup G, SmallRankSBSylow p f x z T E → E ⊓ M = ⊥
  iii : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G) (f : ℕ),
    Lemma630Hyp G p P M x z T f → Lemma630Iii p f x

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.RankThreeTheoremC
