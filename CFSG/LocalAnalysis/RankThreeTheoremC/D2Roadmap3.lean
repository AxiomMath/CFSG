module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L2Case3
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeOut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem d2ComponentCaseMax3_of_cases3 (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (hsq : D2CaseL2Square3 G) (hU3 : D2CaseU33 G) (hexc : D2SeitzExc3 G)
    (hAlt : ∀ (p : ℕ) (hp : 5 ≤ 2 * p), D2IndexCase3 G (.alternating (2 * p) hp))
    (hSpor : D2SporadicCase3 G) : D2ComponentCaseMax3 G :=
  d2ComponentCaseMax3_of_families3 (d2AltCase3_of_twoMul hAlt)
    (d2LieCase3_of hS (d2IndexCaseAt3_lie_char_of hrank kFactLieCharOut kFactLinTwoPrimeRank
      kFactLinThreeCore hsq hU3) hexc) hSpor

theorem d2ComponentCaseMax3_of_current3 (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (hZ : D2TheoremZ3 G) (hMS : D2L2MSide3 G) (hU3 : D2CaseU33 G) (hexc : D2SeitzExc3 G)
    (hAltNo : D2AltNoConfig3 G) (hA6 : D2AltSixCase3 G) (hSpor : D2SporadicCase3 G) :
    D2ComponentCaseMax3 G :=
  d2ComponentCaseMax3_of_cases3 hrank hS (d2CaseL2Square3_of_leaves hrank hS hexc hSpor hZ hMS)
    hU3 hexc (d2IndexCase3_alt_of hAltNo hA6) hSpor

theorem pRank_inf_le_three_of_setting (hS : Setting G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {H : Subgroup G} (hH : IsTwoLocal H) (M : Subgroup G) : CFSG.Open.pRank q (H ⊓ M) ≤ 3 := by
  have h1 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq (inf_le_left : H ⊓ M ≤ H)
  have h2 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank q hq hq2 H hH
  rw [hS.rank] at h2
  omega

theorem glbBetaFour_eq_empty_of_setting (hS : Setting G) : GLBBetaFour G = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  have h := CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_le_evenRank (G := G) p hp.1
    hp.2.1
  have h4 : 4 ≤ rankThreeLocalRank p G := hp.2.2.2
  rw [hS.rank] at h
  omega

theorem d1For_of_setting (hS : Setting G) : D1For G := fun p hp =>
  (Set.eq_empty_iff_forall_notMem.mp (glbBetaFour_eq_empty_of_setting hS) p hp).elim

theorem glbPreuniqueness_of_setting (hS : Setting G) : GLBPreuniqueness G := fun q hq =>
  (Set.eq_empty_iff_forall_notMem.mp (glbBetaFour_eq_empty_of_setting hS) q hq).elim

end CFSG.LocalAnalysis.RankThreeTheoremC
