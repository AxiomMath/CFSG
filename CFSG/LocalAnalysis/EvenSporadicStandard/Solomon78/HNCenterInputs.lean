module

public import CFSG.Sporadic.HNOddCore.InvArrays

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.HNOddCore.InvData

@[expose] def hnFixCheck : Bool :=
  (List.range 800).all fun k =>
    (k == 0) == (List.range 9).all fun s => (s4Perms[s]!)[k]! == k

end CFSG.EvenSporadicStandard.Solomon78
