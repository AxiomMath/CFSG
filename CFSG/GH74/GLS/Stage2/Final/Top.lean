module

public import CFSG.GH74.GLS.Stage2.Final.M12
public import CFSG.GH74.GLS.Stage2.Final.G2
public import CFSG.GH74.GLS.Stage2.Final.Four

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Glue CFSG.GH74.GLS.Stage1.Main

theorem s_stage4_Std_of_stage12
    (hIV3 : ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeaf x Kb)
    (hIV3A7 : ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeafA7 x Kb)
    (h91 : Sec14.IVK_9_1) (h144 : Prod.Lemma14_4) (h145 : Prod.Lemma14_5) (h1 : Stage1OutThree)
    (hmain : Stage2Main) : S_stage4_Std :=
  s_stage4_Std_of_main hIV3 hIV3A7 h91 h144 h145 hmain (s_stage4_G2_Std_of_stage1 h1 hmain)

theorem s_stage2Four_Std_of_stage12 (hno : S_noTwoAnNineTen) (hcl : ClassicalData) (h1 : Stage1OutFour)
    (hmain : Stage2Main) : S_stage2Four_Std :=
  s_stage2Four_Std_of_stage1 hno hcl h1 hmain

end CFSG.GH74.GLS.Stage2.Final
