module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem stmt5_1_10_of_F4 (h331 : Stmt3_3_1_F4) (hE22 : E2.E22StatementC)
    (hTr : Stmt5_1_10_E22) : Stmt5_1_10_F4 := by
  intro G _ _ T M L H B D n hyp hN
  have h := hyp.toHyp5_0_1
  obtain ⟨hmp, -⟩ := h.minParabolic_of_isHStar_F4 h331 hyp.hStar
  obtain ⟨hns', hsqtk⟩ := h.not_isSolvable_and_sqtk_of_lie hyp.hStar hyp.lieQuot
  obtain ⟨⟨K, hKc, hHK, hq, hcases⟩, -⟩ := hE22.exists_cases hmp hsqtk hns'
  obtain ⟨k, hk, hfc⟩ := E22CasesC.exists_field_of_lie hmp.isSylow.1 hmp.isSylow.2.1 hKc hHK
    hyp.lieQuot hcases
  obtain ⟨hKeq, hBorel, hc⟩ := hTr G T M L H B D K n k hyp hN hKc hHK hq hfc
  exact ⟨k, hk, hBorel, isHallTwoPrimeOf_inf_oTwoUpper hN.1, K, hKc, hKeq, hc⟩

end CFSG.Quasithin.H13
