module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenTwoLocalPSp
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenTwoLocalOmega
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenTwoLocalPSU

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem overgroupLocalAt_of_when_univ {t : StatedLieTag}
    (h : OvergroupLocalWhen t (fun _ _ => True)) : OvergroupLocalAt t := by
  intro K _ _ hs hab n f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf
  exact h K hs hab n f f₀ p trivial hadm hmodel ht hp hp5 hpK hdiv hf

theorem overgroupLocalAt_POmegaOdd : OvergroupLocalAt .POmegaOdd := by
  intro K _ _ _ _ n f f₀ p hadm
  exact absurd hadm.2.2.2 (by norm_num)

theorem overgroupLocalAt_twistedG2 : OvergroupLocalAt .twistedG2 := by
  intro K _ _ _ _ n f f₀ p hadm
  exact absurd hadm.2.2.2.1 (by norm_num)

theorem overgroupLocalAt_POmegaMinus (hOver : CFSG.Quasithin.AsLieTwoOvergroups)
    (hLie : LieOrderFormulasInput) : OvergroupLocalAt .POmegaMinus :=
  overgroupLocalAt_of_when_univ
    (overgroupLocalWhen_of_twoLocalWhen hOver (twoLocalWhen_POmegaMinus hLie))

theorem overgroupLocalAt_PSL (hOver : CFSG.Quasithin.AsLieTwoOvergroups)
    (hexc : OvergroupLocalWhen .PSL (IsExcRow .PSL)) : OvergroupLocalAt .PSL :=
  overgroupLocalAt_of_when (IsExcRow .PSL) hexc
    (overgroupLocalWhen_of_twoLocalWhen hOver twoLocalWhen_PSL)

theorem overgroupLocalAt_PSp (hOver : CFSG.Quasithin.AsLieTwoOvergroups)
    (hLie : LieOrderFormulasInput) (hexc : OvergroupLocalWhen .PSp (IsExcRow .PSp)) :
    OvergroupLocalAt .PSp :=
  overgroupLocalAt_of_when (IsExcRow .PSp) hexc
    (overgroupLocalWhen_of_twoLocalWhen hOver (twoLocalWhen_PSp hLie))

theorem overgroupLocalAt_PSU (hOver : CFSG.Quasithin.AsLieTwoOvergroups)
    (hLie : LieOrderFormulasInput)
    (hrest : OvergroupLocalWhen .PSU (fun n f₀ => ¬ (Odd n ∧ ¬ IsExcRow .PSU n f₀))) :
    OvergroupLocalAt .PSU :=
  overgroupLocalAt_of_when (fun n f₀ => Odd n ∧ ¬ IsExcRow .PSU n f₀)
    (overgroupLocalWhen_of_twoLocalWhen hOver (twoLocalWhen_PSU_odd hLie)) hrest

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
