module

import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

section Rank

variable {G : Type*} [Group G]

variable [Finite G]

theorem pRank_le_pRank_sylow {p : ℕ} (hp : p.Prime) (P : Sylow p G) (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (P : Subgroup G) := by
  have hPT : ∀ T : Sylow p G, CFSG.Open.pRank p (T : Subgroup G) =
      CFSG.Open.pRank p (P : Subgroup G) := fun T => sylow_pRank_eq p hp T P
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro k ⟨E, hEH, hE, hEc⟩
  obtain ⟨T, hT⟩ := (elementary_isPGroup p E hE).exists_le_sylow
  have hkT : k ≤ CFSG.Open.pRank p (T : Subgroup G) := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hp.one_lt _) ⟨E, hT, hE, hEc⟩
  rw [hPT T] at hkT
  exact hkT

end Rank

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.RankThreeTheoremC
