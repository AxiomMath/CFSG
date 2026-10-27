module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4CoreIU
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4CoreII
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4CoreField

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.GH74.GLS.Stage12

theorem psp4Core_thm : PSp4Core :=
  psp4Core_of_classes coreInner_thm coreI_thm coreII_thm coreField_thm

theorem cell87_FSp4_thm (hInv : InvSec) : Cell87 FSp4 :=
  cell87_FSp4 hInv psp4Core_thm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
