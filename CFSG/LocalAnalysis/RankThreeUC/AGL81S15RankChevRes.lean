module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevResStmt
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSp
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevOrth

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem lieOddRankChev_of_parts (hG : CFSG.Open.GriessAllModelsStatement)
    (hLE : LieOddRankChevLinEasy) (hUE : LieOddRankChevUniEasy) (hRes : LieOddRankChevRes) :
    LieOddRankChev := by
  intro K _ _ hq d hd he r hr hr2
  obtain ⟨d1, hv⟩ := d
  obtain ⟨e⟩ := he
  cases d1 with
  | A l Q =>
    by_cases hc : r ∣ Q.card - 1 ∧ r ∣ l + 1
    · exact hRes.1 K hq l Q hv hd ⟨e⟩ r hr hr2 hc
    · exact hLE K hq l Q hv hd ⟨e⟩ r hr hr2 hc
  | twistedA l Q =>
    by_cases hc : r ∣ Q.card + 1 ∧ r ∣ l + 1
    · exact hRes.2.1 K hq l Q hv hd ⟨e⟩ r hr hr2 hc
    · exact hUE K hq l Q hv hd ⟨e⟩ r hr hr2 hc
  | B l Q => exact pRank_chev_B hG hq hv hd e hr hr2
  | C l Q => exact hd.elim
  | D l Q => exact pRank_chev_D hG hq hv hd e hr hr2
  | twistedD l Q => exact pRank_chev_twistedD hG hq hv hd e hr hr2
  | E6 Q => exact hd.elim
  | E7 Q => exact hd.elim
  | E8 Q => exact hd.elim
  | F4 Q => exact hd.elim
  | G2 Q => exact hRes.2.2 K hq Q hv hd ⟨e⟩ r hr hr2
  | twistedE6 Q => exact hd.elim
  | trialityD4 Q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 m => exact hd.elim
  | reeF4 m => exact hd.elim
  | tits => exact hd.elim

end CFSG.LocalAnalysis.RankThreeUC.S15
