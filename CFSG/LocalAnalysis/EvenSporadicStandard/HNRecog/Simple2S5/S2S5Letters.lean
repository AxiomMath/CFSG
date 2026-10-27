module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5YData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5TData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

@[expose] def expandL (subs : List (List Nat)) (l : List Nat) : List Nat :=
  l.flatMap fun i => subs.getD (i - 1) []

@[expose] def yWord (k i : Nat) : List Nat := (ykWords.getD k []).getD i []

@[expose] def tWords (k : Nat) : List (List Nat) :=
  (tLetters.getD k []).map (expandL (ykWords.getD k []))

@[expose] def mWords (k : Nat) : List (List Nat) :=
  (mLetters.getD k []).map (expandL (ykWords.getD k []))

@[expose] def uWord (k : Nat) : List Nat := expandL (ykWords.getD k []) (uLetters.getD k [])

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
