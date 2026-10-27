module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveRepData

public section

namespace CFSG.KC.KDenseP.MonFive

open CFSG.Monster.AxisCount CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive

@[expose] def tri3 (eqs nes : List (List Native.Gen × List Native.Gen)) :
    List (List Native.Gen × List Native.Gen) :=
  eqs ++ eqs ++ eqs ++ nes

@[expose] def nesOf (lo n : ℕ) : List (List Native.Gen × List Native.Gen) :=
  (List.range n).filterMap fun i =>
    if (fiveReps[lo + i]!).kind then none
    else some ((fiveReps[lo + i]!).wa ++ (fiveReps[lo + i]!).wb, [])

end CFSG.KC.KDenseP.MonFive

end
