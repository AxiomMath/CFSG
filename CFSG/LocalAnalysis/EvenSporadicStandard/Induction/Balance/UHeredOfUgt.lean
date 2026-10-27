module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

theorem UHered.of_ugt (h : UGTSimpleStatement) (H : Type) [Group H] : UHered H :=
  fun S _ _ _ _ => h S

end CFSG.EvenSporadicStandard.Induction.Balance
