module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.Noncat
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Unconditional2

public section

namespace CFSG.EvenSporadicStandard.Induction

section Certified


theorem sol78Thm46SuzEven_holds : Sol78Thm46SuzEven :=
  fun _ _ _ _ hL hZ hS => (TwoSuz.twoSuz_not_standard_unconditional hL hZ hS).elim

end Certified

end CFSG.EvenSporadicStandard.Induction
