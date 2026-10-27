module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeList

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G] {p : ℕ}

structure AGL81NineAt (p : ℕ) (M H N : Subgroup G) : Prop where
  core_le : (primeComplementCore (G := N) p).map N.subtype ≤ M
  nineThree : Hyp111NineThree p M N (d1KBar p M N)
  list : NineThreeListAt p M N
  nineSeventeen : Hyp917At p M H N (d1KBar p M H)
  kappa_le : d1Kappa p M H ≤ d1Kappa p M N

variable (G) in
@[expose] def AGL81NineCompetitor : Prop :=
  AGLGlobal G → ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G), D1Escape p P M H R →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) →
    ∀ B N : Subgroup G, IsAGLQ p M B → B ≤ H → GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N →
      AGLCovers p H N (d1KBar p M H) → AGL81NineAt p M H N

theorem AGL81NineAt.hyp93At {M H N : Subgroup G} (h : AGL81NineAt p M H N) : Hyp93At p M N :=
  ⟨h.nineThree.factor, h.core_le⟩

theorem aglCovers_self (H : Subgroup G) (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
    AGLCovers p H H K := by
  intro x _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := H) p) x
  exact ⟨y, by simp [Subgroup.mem_subgroupOf], rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
