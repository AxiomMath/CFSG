module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
import CFSG.LocalAnalysis.AGLEmbedding.AThreePLift
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGen

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore local_pRank_le_evenRank)

variable {G : Type} [Group G] [Finite G]

theorem d1CaseThreeA3pSeven3 : D1CaseThreeA3pAt3 G (7 ≤ ·) := by
  intro p _ P M H R Rbar hcfg hp7 K hK huniq hnc hcent hKD hZ he
  obtain ⟨ι, hι⟩ := exists_injective_of_center_eq_bot hZ he
  obtain ⟨Y₇, hY₇, hr₇⟩ := exists_rank_seven hp7 hι
  have h4 : 3 < CFSG.Open.pRank 3 H :=
    lt_pRank_of_quotient thompsonNormalAbelianGen (by norm_num) (primeComplementCore (G := H) p)
      hY₇ (Subgroup.map_subtype_le _) (r := 3) (by rw [hr₇]; norm_num)
  have h3 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) H hcfg.ext.maxTwoLocal_H.1
  rw [hcfg.glob.rank] at h3
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
