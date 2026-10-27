module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PerfectData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Perfect

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic


theorem solomonCoreP_co1 : SolomonCoreP .Co1 Co1Q :=
  solomonCoreP_of_perfect .Co1 Co1Q co1Q_inL co1Q_twoSylow perfectRowData_co1 tMemFStar_co1

theorem sol78Closing_co1 (hmult : OddMultTrivial .Co1) :
    Sol78Closing [.Co1] (fun _ => Co1Q) :=
  sol78Closing_of_partsP (S := [.Co1]) (Q := fun _ => Co1Q) (P := fun _ => Co1Pair)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78SettingLocalQ_co1 hmult)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78Local39Q_co1 hmult)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact solomonCoreP_co1)

end CFSG.EvenSporadicStandard.Induction
