module

public import CFSG.Sporadic.J4.QT2LocZCentNative

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

@[expose] def ZfGens : Prop :=
  zcLocWf = true ∧ ∀ g < 3, lenOK (zcGenTabs.getD g []) = true ∧ actT (zcGenTabs.getD g []) 1 = 1

end CFSG.QuasithinUnique.A5
