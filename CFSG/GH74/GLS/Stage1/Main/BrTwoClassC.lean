module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassB

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial

theorem psp4TwoClass_proved (hII : II4_4_4_center) (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6)
    (hpnf : P_normal_four) (hL44 : Lemma4_4) (hL45 : Lemma4_5) (h31 : IVK_3_1a_lifted)
    (h73 : Lemma7_3) (h74 : Lemma7_4) (h77 : Lemma7_7) : PSp4TwoClass :=
  fun G _ _ z S q hcen hT L₁ L₂ hpair => by
    obtain ⟨x, hx⟩ :=
      psp4_core_exists hII h41 h61 h66 hpnf hL44 hL45 h31 h73 h74 h77 hcen hT hpair
    exact ⟨x, TwoClassData.of_core hx⟩

end CFSG.GH74.GLS.Stage1.Main
