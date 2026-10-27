module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCasesLin
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCasesOther

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem mRank3_cases {d : TauCeti.LieTypeIndex} (hd : IsRankTwoPlus d) (z : ℕ) : Rk3Cases d z := by
  cases d with
  | A l Q => exact rk3Cases_A hd.1 hd.2 z
  | twistedA l Q => exact rk3Cases_tA hd.1 hd.2 z
  | B l Q => exact rk3Cases_B hd.1 hd.2 z
  | D l Q => exact rk3Cases_D hd.1 hd.2 z
  | twistedD l Q => exact rk3Cases_tD hd.1 hd.2 z
  | G2 Q => exact rk3Cases_G2 hd z
  | _ => exact hd.elim

end CFSG.LocalAnalysis.RankThreeUC.S15
