module

public section

namespace CFSG.EvenSporadicStandard.Induction.RuSz

@[expose] def x0Word : String := "babbaBabaBaBabaBabaBaBabaB"

@[expose] def n1Word : String := "aBabaBabaBaBabaBabbabaBababa"

@[expose] def n2Word : String := "ababbabbabaBabaBababbabaBaBa"

@[expose] def hBWords : List String :=
  ["BabbaBababbab", "abbaBabaBaBaba", "aBabbaBabbabaBaBab"]

@[expose] def k1Word : String := "BabaBabbaBababbaBababbabb"

@[expose] def borelGens : List String := [n1Word, n2Word] ++ hBWords ++ [k1Word]

end CFSG.EvenSporadicStandard.Induction.RuSz
