module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevResStmt
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevLin
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
import CFSG.LargeExtraspecial.DWFldLinear

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace RankChevLinEasyProof

theorem cast_ne_zero_of_card_two_pow {F : Type} [Field F] [Finite F] {f r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hF : Nat.card F = 2 ^ f) : (r : F) ≠ 0 := by
  haveI : CharP F 2 := CFSG.LargeExtraspecial.DW.charP_two_of_card_eq hF
  intro h
  have h2 : 2 ∣ r := (CharP.cast_eq_zero_iff F 2 r).1 h
  exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1 h2).symm

end RankChevLinEasyProof

open RankChevLinEasyProof CFSG.Open in
theorem pRank_chev_A_dvd_not_dvd_m (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A l Q, hv⟩)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hc1 : r ∣ Q.card - 1) (hc2 : ¬ r ∣ l + 1) :
    CFSG.Open.pRank r (⊤ : Subgroup K) =
      rkLin (l + 1) true Q.card r (Nat.card (Subgroup.center K)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨F, instF, instFin, hF, hrank⟩ := chevA_reduce_to_SL hG hq hv hQ e hr hr2
    (fun h => hc2 (h.trans (Nat.gcd_dvd_left _ _)))
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hFn : Nat.card F = 2 ^ Q.exponent := by rw [Nat.card_eq_fintype_card, hF, hQc]
  have hrF : (r : F) ≠ 0 := cast_ne_zero_of_card_two_pow hr hr2 hFn
  have hdvd : r ∣ Nat.card F - 1 := by rw [Nat.card_eq_fintype_card, hF]; exact hc1
  rw [hrank, pRank_top_statedSL_eq_pred (by omega) hrF hdvd]
  have h1 : eP Q.card r = 1 := (eP_eq_one_iff (by rw [hQc]; exact Nat.one_le_two_pow)).2 hc1
  rw [rkLin, if_pos (by simpa using h1), if_neg (fun h => hc2 h.2.1)]
  rfl

open CFSG.Open in
theorem lieOddRankChevLinEasy_holds (hG : CFSG.Open.GriessAllModelsStatement) :
    LieOddRankChevLinEasy := by
  intro K _ _ hq l Q hv hQ he r hr hr2 hc
  obtain ⟨e⟩ := he
  by_cases h1 : r ∣ Q.card - 1
  · exact pRank_chev_A_dvd_not_dvd_m hG hq hv hQ e hr hr2 h1 fun h2 => hc ⟨h1, h2⟩
  · exact pRank_chev_A_largeE hG hq hv hQ e hr hr2 h1

end CFSG.LocalAnalysis.RankThreeUC.S15
