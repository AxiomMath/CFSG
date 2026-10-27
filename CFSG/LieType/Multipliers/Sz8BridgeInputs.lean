module

public import Mathlib.Data.Nat.Notation
public import CFSG.LieType.Multipliers.Sz8Matrix
public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting

@[expose] public section

namespace CFSG.LieType.Multipliers.Sz8

open TauCeti CFSG.CosetTable

@[expose] def parseWord (s : String) : List (Fin 2 × Bool) :=
  s.toList.filterMap fun c =>
    if c = 'a' then some (0, true) else if c = 'A' then some (0, false)
    else if c = 'b' then some (1, true) else if c = 'B' then some (1, false) else none

@[expose] def relFive : String := "ababbabbaBababbabbaBababbabbaBababbabbaBababbabbaB"

@[expose] def relSeven : String := "abaBabbabaBabbabaBabbabaBabbabaBabbabaBabbabaBabb"

@[expose] def relStrings : List String :=
  ["aa", "bbbb", "ababababab", "abbabbabbabbabbabbabb", relFive, relSeven]

@[expose] def rels : List (List (Fin 2 × Bool)) := relStrings.map parseWord

@[expose] def genWords : List String :=
  ["", "aBababbaBabbaBabaBaba", "bb", "aBababbaBabbaBabaBababb", "abaBabbaBabbabaBabbaBabbabb",
    "ababbabaBabaBababbabbaBabbabaB", "abaBabbaBabbabaBabbaBabba", "abbaBabbabaBabbabaBabaBaBaba",
    "babbaBabaBaBabaBabbabaBaBaba", "abbaBabbabaBaBabaBabaBaBabaB", "abbabaBaBababbabaBabaBabaBa",
    "abaBabaBabaBabbabbaBabbabba", "abbaBabaBaBabaBabbabaBaBabab", "BabbaBabbabaBaBabaBabaBaBaba",
    "abbaBabaBaBabaBabbabaBaBabaB", "babbaBabbabaBaBabaBabaBaBaba", "babaBabaBabaBabbabbaBabbabba",
    "abbaBabaBaBabaBabbabaBaBaba", "BabaBabaBabaBabbabbaBabbabba", "BabbabaBaBababbabaBabaBabaBa",
    "abaBabaBabaBabbabbaBabbabbab", "abbabaBaBababbabaBabaBabaBab", "abbaBabbabaBaBabaBabaBaBaba",
    "abbabaBaBababbabaBabaBabaBaB", "b", "aBababbaBabbaBabaBabab", "B", "aBababbaBabbaBabaBabaB",
    "abaBabbaBabbabaBabbaBabbaB", "ababbabaBabaBababbabbaBabbaba", "abaBabbaBabbabaBabbaBabbab",
    "abbaBabbabaBabbabaBabaBaBabab", "aBaBababbaBabbabbabaBabab", "baBabaBabbabaBaBababbaBaB",
    "aBaBababbaBabbabbabaBabaB", "baBabaBabbabaBaBababbaBab", "aBabaBabbabaBaBababbaBabb",
    "ababbabbaBabbabbabaBaba", "aBabaBabbabaBaBababbaBa", "ababbabbaBabbabbabaBababb",
    "ababaBabbaBabbabaBabbabaBabbab", "abaBabaBababbabbaBabbabaBabbaB",
    "ababaBabbaBabbabaBabbabaBabbaB", "aBabbabbaBabbabaBabbabaBabba",
    "abbabaBabaBaBababbaBabaBabaBaB", "abbabaBabbabaBabaBabbaBabbaBab",
    "abbabaBabaBaBababbaBabaBabaBab", "abbabaBabbabaBabaBaBababbaba",
    "BabbabaBabbabaBabaBaBababbaba", "abbabaBabbabaBabaBabbaBabbaBa",
    "abbabaBabaBaBababbaBabaBabaBa", "abbabaBabbabaBabaBaBababbabaB",
    "ababaBabbaBabbabaBabbabaBabba", "aBabbabbaBabbabaBabbabaBabbab",
    "baBabbabbaBabbabaBabbabaBabba", "abaBabaBababbabbaBabbabaBabba", "baBabaBabbabaBaBababbaBa",
    "BababbabbaBabbabbabaBaba", "BaBabaBabbabaBaBababbaBa", "aBaBababbaBabbabbabaBaba",
    "ababbabbaBabbabbabaBabab", "aBabaBabbabaBaBababbaBaB", "ababbabbaBabbabbabaBabaB",
    "aBabaBabbabaBaBababbaBab"]

@[expose] def F8.code (c : F8) : ℕ := c.c0.val + 2 * c.c1.val + 4 * c.c2.val

@[expose] def genWord (c d : F8) : List (Fin 2 × Bool) :=
  parseWord (genWords.getD (8 * c.code + d.code) "")

@[expose] def allF8 : List F8 :=
  [⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨1, 1, 0⟩, ⟨0, 0, 1⟩, ⟨1, 0, 1⟩, ⟨0, 1, 1⟩, ⟨1, 1, 1⟩]

@[expose] def matCheck (ws : List (List (Fin 2 × Bool))) : Bool :=
  ws.all fun w => decide (wordArr w = ofMat 1)

@[expose] def genCheck : Bool :=
  allF8.all fun c => allF8.all fun d => decide (ofMat (rootMat c d) = wordArr (genWord c d))

end CFSG.LieType.Multipliers.Sz8
