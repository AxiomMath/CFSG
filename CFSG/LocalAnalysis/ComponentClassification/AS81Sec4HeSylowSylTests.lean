module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowTests

public section

namespace CFSG.ComponentClassification.AS81.HeSylow

open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.Native

@[expose] def sylCheck8330S : Bool :=
  heSylWords.length == 5 &&
    allLt 5 (fun i => lettersOK 9 (heSylWords.getD i [])) &&
    allLt 9 (fun j => validA 8330 heSylLetters[j]!)

@[expose] def heSylowCheckS : Bool := sylCheck8330S && sylCheckRestrict && sylCheck16

end CFSG.ComponentClassification.AS81.HeSylow
