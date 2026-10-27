module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.Sporadic.Bridge.Catalogue

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem sporadicLocalCensus_holds
    : SporadicLocalCensus :=
  sporadicLocalCensus_of_bridges (hB := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group)

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
