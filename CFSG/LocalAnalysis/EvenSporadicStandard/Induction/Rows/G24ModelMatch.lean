module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutBase

public section

namespace CFSG.EvenSporadicStandard.G24Model

open CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.G24Aut

@[expose] def pgArrs : Array (Array Nat) :=
  Array.ofFn (n := 16) fun j => Array.ofFn (n := nLines) fun k => pgNum j k

@[expose] def matchOK : Bool :=
  waWord.all (· < 16) && wbWord.all (· < 16) &&
    eqA nn (prodA pgArrs waWord) xa && eqA nn (prodA pgArrs wbWord) ya

end CFSG.EvenSporadicStandard.G24Model
