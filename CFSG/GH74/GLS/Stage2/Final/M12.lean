module

public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12Branch
public import CFSG.GH74.GLS.Stage12.Branches

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Glue

theorem stage2OddCoreM12_of_main (h : Stage2Main) : Prod.Stage2OddCoreM12 := by
  intro G _ _ z S hctx
  exact (h G z Kind.m12 S hctx).oddCore (fun ε h' => by cases h')

theorem s_stage1_thm6_Std_of_main
    (hIV3 : ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeaf x Kb)
    (hIV3A7 : ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeafA7 x Kb)
    (h91 : Sec14.IVK_9_1) (h144 : Prod.Lemma14_4) (h145 : Prod.Lemma14_5) (hmain : Stage2Main) :
    S_stage1_thm6_Std :=
  Prod.s_stage1_thm6_Std_of_stage2 hIV3 hIV3A7 h91 h144 h145 (stage2OddCoreM12_of_main hmain)

theorem s_stage4_Std_of_main
    (hIV3 : ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeaf x Kb)
    (hIV3A7 : ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeafA7 x Kb)
    (h91 : Sec14.IVK_9_1) (h144 : Prod.Lemma14_4) (h145 : Prod.Lemma14_5) (hmain : Stage2Main)
    (hg2 : S_stage4_G2_Std) : S_stage4_Std :=
  s_stage4_Std_of_branches (s_stage1_thm6_Std_of_main hIV3 hIV3A7 h91 h144 h145 hmain) hg2

end CFSG.GH74.GLS.Stage2.Final
