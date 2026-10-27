module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevResStmt
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevUni
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevLinEasy
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open RankChevLinEasyProof CFSG.Open in
theorem pRank_chev_twistedA_dvd_not_dvd_m (hG : CFSG.Open.GriessAllModelsStatement) {K : Type}
    [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA l Q, hv⟩)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hc1 : r ∣ Q.card + 1) (hc2 : ¬ r ∣ l + 1) :
    CFSG.Open.pRank r (⊤ : Subgroup K) =
      rkLin (l + 1) false Q.card r (Nat.card (Subgroup.center K)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨F, instF, instFin, hF, hrank⟩ := chevU_reduce_to_SU hG hq hv hQ e hr hr2
    (fun h => hc2 (h.trans (Nat.gcd_dvd_left _ _)))
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hFn : Nat.card F = Q.card ^ 2 := by rw [Nat.card_eq_fintype_card, hF]
  have hFn2 : Nat.card F = 2 ^ (Q.exponent * 2) := by rw [hFn, hQc, ← pow_mul]
  have hrF : (r : F) ≠ 0 := cast_ne_zero_of_card_two_pow hr hr2 hFn2
  rw [hrank, pRank_top_statedSU_eq_pred (by omega) hrF hFn hc1]
  have h1 : eM Q.card r = 1 := eM_eq_one_iff.2 hc1
  rw [rkLin, if_pos (by simpa using h1), if_neg (fun h => hc2 h.2.1)]
  rfl

open CFSG.Open in
theorem lieOddRankChevUniEasy_holds (hG : CFSG.Open.GriessAllModelsStatement) :
    LieOddRankChevUniEasy := by
  intro K _ _ hq l Q hv hQ he r hr hr2 hc
  obtain ⟨e⟩ := he
  by_cases h1 : r ∣ Q.card + 1
  · exact pRank_chev_twistedA_dvd_not_dvd_m hG hq hv hQ e hr hr2 h1 fun h2 => hc ⟨h1, h2⟩
  · exact pRank_chev_twistedA_largeE hG hq hv hQ e hr hr2 h1

end CFSG.LocalAnalysis.RankThreeUC.S15
