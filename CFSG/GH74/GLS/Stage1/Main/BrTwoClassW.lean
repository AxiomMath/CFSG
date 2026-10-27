module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassX

public section

namespace CFSG.GH74.GLS.Stage1.Main

open CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7

theorem l4nfRest_proved (hII : II4_4_4_center) (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6)
    (hpnf : P_normal_four) (hL44 : Lemma4_4) (hL45 : Lemma4_5) (h31 : IVK_3_1a_lifted)
    (h72 : Prop7_2) (h73 : Lemma7_3) (h74 : Lemma7_4) (h77 : Lemma7_7) (h31c : IVK_3_1c_lifted) :
    L4NFRest :=
  l4nfRest_of_induced_good hII h41 h61 h66 hpnf hL44 hL45 h31 h72 h73 h74 h77
    (l4nfInduced_proved hII h41 h61 h66 hpnf hL44 hL45 h72) (l4nfGood_proved hII h41 h72 h31c)

end CFSG.GH74.GLS.Stage1.Main
