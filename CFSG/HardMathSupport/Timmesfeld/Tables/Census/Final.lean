module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcCensus
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.U3Aut

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem tableL2_unconditional
    : TableL2 :=
  tableL2_holds sporadicLocalCensus_holds exceptionalLieCensus_holds

theorem t9Lie_unconditional
    : T9Lie :=
  t9Lie_holds exceptionalLieCensus_holds u3AutRankLeTwo_holds

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
