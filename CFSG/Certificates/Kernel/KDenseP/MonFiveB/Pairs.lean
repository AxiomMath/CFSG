module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.MonsterFiveBWitData

public section

namespace CFSG.KC.KDenseP.MonFiveB

open CFSG.Monster.AxisCount CFSG.HardMathSupport.Dickson.I271.MonsterFiveB

@[expose] def tri (b : List ℕ) : List (List Native.Gen × List Native.Gen) :=
  bEqsOf b ++ bEqsOf b ++ bEqsOf b ++ []

end CFSG.KC.KDenseP.MonFiveB

end
