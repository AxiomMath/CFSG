module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.HSMcLLyHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.StdUHered

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem HSMcLLyExclusionHered.of_std (h : HSMcLLyExclusionHered)
    (hU : Induction.Balance.StdUHered) : HSMcLLyExclusion :=
  fun G _ _ L hL => h G (hU G L hL) L hL

end CFSG.EvenSporadicStandard
