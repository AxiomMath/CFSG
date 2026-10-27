module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveData

@[expose] public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative

set_option compiler.extract_closed false

@[expose] def cubeProd (X Y C : Array V4) (i j k : Nat) : Array V4 :=
  mulRows (mulRows (powRowsN X i) (powRowsN Y j)) (powRowsN C k)

end CFSG.HardMathSupport.Dickson.I271
