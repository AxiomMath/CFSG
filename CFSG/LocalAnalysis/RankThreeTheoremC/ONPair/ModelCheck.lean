module

public import CFSG.RankThree.Native.ONSevenArrays
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ModelData
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.AlphaCheck
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.SL3Pres
public import CFSG.Sporadic.Schreier.ONCheckChain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.RankThree.Native
open CFSG.ClassicalInvolution.Phan.Q3G (decodeWord)

@[expose] def codeLetters (w : List (Fin 4 × Bool)) : List Int :=
  w.map fun l => if l.2 then (l.1.val : Int) + 1 else -((l.1.val : Int) + 1)

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
