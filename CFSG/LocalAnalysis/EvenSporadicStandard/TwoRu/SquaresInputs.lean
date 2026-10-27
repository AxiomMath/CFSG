module

public import CFSG.Sporadic.Schreier.RuCheckInvInputs

public section

namespace CFSG.EvenSporadicStandard.TwoRu

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruSquareTest (t : Array ℕ) : Bool :=
  !eqA 4060 (powA 4060 t 4) (idA 4060) || eqA 4060 (compA 4060 t t) (idA 4060) ||
    decide (0 < ruFixCount (compA 4060 t t))

@[noinline, expose] def ruSquareCheck : Bool := all2 4060 ruLevS ruSquareTest

end CFSG.EvenSporadicStandard.TwoRu
