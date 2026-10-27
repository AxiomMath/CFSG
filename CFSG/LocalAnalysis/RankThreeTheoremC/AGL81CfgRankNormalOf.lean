module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem pRank_three_inf_le_of_cfg (hS : Setting G) {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K) :
    CFSG.Open.pRank 3 (H ⊓ M) ≤ 3 := by
  refine (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) inf_le_left).trans ?_
  have h2 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) H hd.maxH.1
  rw [hS.rank] at h2
  exact h2

theorem agl81TenNineRankCfg_holds : AGL81TenNineRankCfg G :=
  fun hS _ _ _ _ _ _ hd _ => pRank_three_inf_le_of_cfg hS hd

end CFSG.LocalAnalysis.RankThreeTheoremC
