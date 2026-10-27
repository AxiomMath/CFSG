module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLFamilies
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLG2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLF4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLE6
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLE7
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLE8
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLTrialityD4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLTwistedF4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLTwistedE6
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSuzuki

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem overgroupLocalAt_of_twoLocalWhen_univ (hOver : CFSG.Quasithin.AsLieTwoOvergroups)
    {t : StatedLieTag} (h : TwoLocalWhen t (fun _ _ => True)) : OvergroupLocalAt t :=
  overgroupLocalAt_of_when_univ (overgroupLocalWhen_of_twoLocalWhen hOver h)

theorem overgroupLocalAt_all
    (hOver : CFSG.Quasithin.AsLieTwoOvergroups) (hLie : LieOrderFormulasInput)
    (t : StatedLieTag) : OvergroupLocalAt t := by
  cases t with
  | PSL => exact overgroupLocalAt_PSL_final hOver
  | PSU => exact overgroupLocalAt_PSU_final hOver hLie
  | PSp => exact overgroupLocalAt_PSp_final hOver hLie
  | POmegaOdd => exact overgroupLocalAt_POmegaOdd
  | POmegaPlus => exact overgroupLocalAt_POmegaPlus_final hOver hLie
  | POmegaMinus => exact overgroupLocalAt_POmegaMinus hOver hLie
  | G2 => exact overgroupLocalAt_of_twoLocalWhen_univ hOver (twoLocalWhen_G2 hLie)
  | F4 => exact overgroupLocalAt_of_twoLocalWhen_univ hOver (twoLocalWhen_F4 hLie)
  | E6 => exact overgroupLocalAt_of_twoLocalWhen_univ hOver (twoLocalWhen_E6 hLie)
  | E7 => exact overgroupLocalAt_of_twoLocalWhen_univ hOver (twoLocalWhen_E7 hLie)
  | E8 => exact overgroupLocalAt_of_twoLocalWhen_univ hOver (twoLocalWhen_E8 hLie)
  | twistedE6 => exact overgroupLocalAt_of_twoLocalWhen_univ hOver (twoLocalWhen_twistedE6 hLie)
  | trialityD4 => exact overgroupLocalAt_of_twoLocalWhen_univ hOver (twoLocalWhen_trialityD4 hLie)
  | twistedB2 => exact overgroupLocalAt_twistedB2
  | twistedG2 => exact overgroupLocalAt_twistedG2
  | twistedF4 => exact overgroupLocalAt_of_twoLocalWhen_univ hOver (twoLocalWhen_twistedF4 hLie)
  | Tits => exact fun K _ _ _ _ n f f₀ p _ _ ht => absurd rfl ht

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
