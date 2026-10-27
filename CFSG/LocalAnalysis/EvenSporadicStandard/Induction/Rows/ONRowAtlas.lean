module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONRankK
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONStage3

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.ONSchreier


theorem on_rowAtlasFacts : RowAtlasFacts [.ONan] (fun _ => ONQ) IsKON where
  pRank_K X _ hX := on_pRank_K X hX
  pRank_L X _ hX := on_pRank_L X hX
  rowExists s hs H _ _ L hcov := by
    rcases List.mem_singleton.1 hs with rfl
    exact on_rowExists H L hcov
  rowFit s hs H _ _ L K hcov hKL hKq hK hstd _ := by
    rcases List.mem_singleton.1 hs with rfl
    exact on_rowFit H L K hcov hKL hKq hK hstd

def stage3Row_on_proved (hfix : ONK2FixedNotLam) : Stage3Row [.ONan] (fun _ => ONQ) :=
  stage3Row_on on_rowAtlasFacts hfix

end CFSG.EvenSporadicStandard.Induction
