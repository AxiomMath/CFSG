module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs

public section

namespace CFSG.EvenSporadicStandard.RuStd

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.RuSchreier
open CFSG.EvenSporadicStandard.TwoRu.HypOne

@[expose] def pairWordG : List ℤ := [2, 3, 2, 3]

@[expose] def pairWordH : List ℤ := [1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 3]

@[expose] def pairTabG : Table := wordT 4060 (letterTab lGens lGensInv) pairWordG

@[expose] def pairTabH : Table := wordT 4060 (letterTab lGens lGensInv) pairWordH

@[expose] def ruPairCheck : Bool :=
  invOK 4060 pairTabG (invT 4060 pairTabG) && invOK 4060 pairTabH (invT 4060 pairTabH) &&
    tblEq 4060 (compT 4060 (compT 4060 (compT 4060 pairTabG pairTabH) (invT 4060 pairTabG))
      (invT 4060 pairTabH)) (tblOfArr (ruRepZA 15))

end CFSG.EvenSporadicStandard.RuStd
