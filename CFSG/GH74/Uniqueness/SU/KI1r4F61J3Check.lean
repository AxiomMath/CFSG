module

public import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def fourGenOK (n : Nat) (gs : List Table) (i j : Nat) : Bool :=
  decide (i < gs.length) && decide (j < gs.length) && gs.all (permOK n) && involOK n gs[i]! &&
    involOK n gs[j]! && commTT n gs[i]! gs[j]! && !tblEq n gs[i]! gs[j]!

end CFSG.GH74.Uniqueness.SU.K.R4
