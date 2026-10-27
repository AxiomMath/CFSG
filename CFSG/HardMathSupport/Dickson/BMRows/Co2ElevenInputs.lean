module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenInputs

public section

namespace CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenNative

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative

set_option compiler.extract_closed false

structure Co2ElevenData where
  words : Array (List Int)
  is : Nat
  ih : Nat
  chain : Array Nat

@[expose] def co2ElevenOK (D : Co2ElevenData) (m bound : Nat) : Bool :=
  let n := 2300
  let T0 := co2T 0
  let T1 := co2T 1
  let L := slpLetters n (co2Gens T0 T1) D.words
  let Y := L[2 * D.is]!
  let ω := ap L[2 * D.ih]! 0
  let base := (Array.range m).map fun i => iterAp Y i ω
  let LC := subLetters L D.chain
  let trees := chainTrees n LC base
  invOK n T0 (invT n T0) && invOK n T1 (invT n T1) && slpOK D.words &&
    decide (D.is < D.words.size) && decide (D.ih < D.words.size) &&
    (List.range D.words.size).all (fun j => invOK n L[2 * j]! L[2 * j + 1]!) &&
    D.chain.all (fun j => decide (j < D.words.size)) && decide (ω < n) && decide (0 < m) &&
    eqTab2 (powT n 11 Y) (idT n) && !(eqTab2 Y (idT n)) &&
    (List.range m).all (fun i => treeOK n base[i]! trees[i]! LC (levelLetters LC base i)) &&
    decide ((List.range m).foldl (fun acc i => acc * trees[i]!.pts.size) 1 = cardCo2 ()) &&
    decide (Nat.count (fun p => sift trees LC (Array.range m) base 0 (tupleOf Y m p) = true) n ≤
      bound)

@[expose] def co2ElevenWordsStr : String :=
  "1;2;4,3;5,3;5,4;7,6;3,7;9,8;3,4;11,10;4,5;13,12;11,4;15,14;11,15;17,16;13,9;19,18;17,3;21,20;\
    3,17;23,22;11,3;25,24;13,23;27,26;11,19;29,28;27,13;31,30;25,21;33,32;25,11;35,34;2;31,29;\
    38,36;-4,-3,-4,-3,-4,-3,4,-3,4,39;38,31;41,39;-3,40,40,-3,-40,-3,-4,42;41,27;44,42;\
    -43,40,40,43,43,43,-4,-43,4,43,40,45;33,35;47,45;40,-46,-46,-43,-4,-43,46,-4,43,48;25,44;\
    50,48;-46,-49,46,46,-49,-40,-46,43,43,49,-3,-49,-46,-3,4,51;33,41;53,51;\
    -49,46,-52,-46,-40,46,52,40,-3,-40,52,40,54;53,47;56,54;\
    -52,-55,-52,-52,-52,-46,-55,-46,-55,-46,-43,46,-52,-3,-40,-4,-3,-49,57;38,33;59,57;\
    -58,-55,-52,55,-58,-46,-52,46,-49,-40,49,49,-52,-4,-40,49,49,60;38,50;62,60;\
    -52,-55,58,46,52,-46,-40,-49,-40,-61,-3,-43,4,63;56,38;65,63;\
    -55,-58,-58,52,52,-46,-49,55,46,40,52,58,-3,40,-49,-4,66"

@[expose] def co2ElevenData : Co2ElevenData where
  words := parseIntLists co2ElevenWordsStr
  is := 33
  ih := 34
  chain := #[0, 1, 37, 40, 43, 46, 49, 52, 55, 58, 61, 64]

@[expose] def co2ElevenCheck (_ : Unit := ()) : Bool := co2ElevenOK co2ElevenData 7 11

end CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenNative
