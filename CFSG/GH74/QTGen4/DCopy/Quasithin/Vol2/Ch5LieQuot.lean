module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL3S
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.Background.E2TwoLieQuotDetect

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt5_2_3_of_S_F4 (h331 : Stmt3_3_1_F4) (hE22 : E2.E22StatementC) (h : Stmt5_2_3S_F4) :
    Stmt5_2_3_F4 := by
  intro G _ _ T M L H V m hsimple hnab hqtke hT hM hTM hLmax hLf hLM hMN h2m hlie hH hn hV
    hVred hVL
  have h501 : Hyp5_0_1 G T M L m :=
    ⟨hsimple, hnab, hqtke, hT, hM, hTM, hLmax, hLf, hLM, hMN, h2m, hlie⟩
  obtain ⟨hmp, hns⟩ := h501.minParabolic_of_isHStar_F4 h331 hH
  obtain ⟨-, hsq⟩ := hns hn
  exact h G T M L H V m hsimple hnab hqtke hT hM hTM hLmax hLf hLM hMN h2m hlie hH
    (E2.exists_hasE22LieQuot_of_one_lt_nParam hE22 hmp hsq hn) hV hVred hVL

end CFSG.Quasithin.H13
