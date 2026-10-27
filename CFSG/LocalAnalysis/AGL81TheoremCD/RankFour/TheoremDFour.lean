module

public import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.WitnessFour
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.NoU4Shape

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankFour

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

variable {G : Type} [Group G] [Finite G]

theorem not_u4Shape_of_witnessFour (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (h : witnessFour G p P M) :
    ¬ CFSG.LocalAnalysis.RankThreeUC.U4Shape p M :=
  not_u4Shape_of_mem_uniqueFourSigma h.2.1

@[expose] def AGL81Section15Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
    CFSG.LocalAnalysis.RankThreeUC.AGL81Residual7NoU4Gen G (witnessFour G)

theorem agl81TheoremDFour_of_section15Four
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hHup : CFSG.LocalAnalysis.RankThreeUC.KFactHuppertProductThree)
    (hI59 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.AGL81I59)
    (h15 : AGL81Section15Four) :
    CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremDFour := by
  intro G _ _ hS4 hU p M hM hp T hT
  obtain ⟨P, hP⟩ := exists_witnessFour hU hM hp
  have hS : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G := Standing4.toGen hS4
  exact agl81TheoremDGen_of_noU4Gen hHup hI59
    (noXBlockFor_of_inputsK h1 h2 h25 hS) hS
    (witnessFour_spec (G := G)) not_u4Shape_of_witnessFour (h15 G hS4 hU) p P M hP T hT

end CFSG.LocalAnalysis.AGL81TheoremCD.RankFour
