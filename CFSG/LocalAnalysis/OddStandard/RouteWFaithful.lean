module

public import CFSG.LocalAnalysis.OddStandard.RouteWAlt
public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulAssembly
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem altStdRankOneW_of_cyclicW
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hCyc : AltStdCyclicW) : AltStdRankOneW := by
  intro G _ _ L hS n hn e hrank
  obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  rcases ComponentClassification.StandardRecognition.standard_centralizer_rank_split
    hS.isStandardSubgroup S with h2 | ⟨hcyc, -⟩ | ⟨r, hr, hq, -⟩
  · exact absurd h2 hrank
  · exact hCyc G L hS n hn e S hcyc
  · obtain ⟨e'⟩ := e
    exact Or.inr (altStd_quaternionW hCIT hS hn e' S hr hq)

end CFSG.OddStandard
