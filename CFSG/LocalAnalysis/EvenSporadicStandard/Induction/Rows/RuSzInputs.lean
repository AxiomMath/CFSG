module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs
public import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs
public meta import Certificates.Data.CFSGNative.Bridge.SurjA

public section

namespace CFSG.EvenSporadicStandard.Induction.RuSz

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.RuSchreier
open CFSG.EvenSporadicStandard.TwoRu.HypOne (lGens lGensInv tblOfArr)

@[expose] def parseW (s : String) : List (ℕ × Bool) :=
  s.toList.filterMap fun c =>
    if c = 'a' then some (0, true) else if c = 'A' then some (0, false)
    else if c = 'b' then some (1, true) else if c = 'B' then some (1, false) else none

@[expose] def szRelStrings : List String :=
  ["aa", "bbbb", "ababababab", "abbabbabbabbabbabbabb",
    "ababbabbaBababbabbaBababbabbaBababbabbaBababbabbaB",
    "abaBabbabaBabbabaBabbabaBabbabaBabbabaBabbabaBabb"]

@[expose] def szRels : List (List (ℕ × Bool)) := szRelStrings.map parseW

@[expose] def sWord : List ℤ := [3, 2, 1, 3, 2, 1]

@[expose] def tWord : List ℤ := [2, 1, 2, 3, 2, 1, 2, 1, 2]

@[expose] def bWord : List ℤ := [2, 3, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 1]

@[expose] def lTab (w : List ℤ) : Table :=
  wordT 4060 (CFSG.EvenSporadicStandard.TwoRu.HypOne.letterTab lGens lGensInv) w

@[expose] def sTab : Table := lTab sWord

@[expose] def tTab : Table := lTab tWord

@[expose] def sInv : Table := invT 4060 sTab

@[expose] def tInv : Table := invT 4060 tTab

@[expose] def bTab : Table := lTab bWord

@[expose] def kTab (w : String) : Table :=
  CFSG.Sporadic.Bridge.TwoGen.Native.wordTab 4060 sTab sInv tTab tInv (parseW w)

@[expose] def conjTab (i : ℕ) (x : Table) : Table :=
  compT 4060 (compT 4060 lGens[i]! x) lGensInv[i]!

@[expose] def normWords : List (ℕ × Bool × String) :=
  [(0, false, "bbabbabaBabaBabaBaBababbab"), (0, true, "abbaBabaBabbaBababbaBaba"),
   (1, false, "aBabbabaBabbabaBabbaba"), (1, true, "BabbabaBabaBabbaBabbabbab"),
   (2, false, "babbabaBabbabaBabbaB"), (2, true, "BabaBaBababbaBabbaBaba")]

@[expose] def hWords : List String :=
  ["BABBABababbab", "ABAbAbABababba", "ABABBABAbbabaBaBab"]

@[expose] def ptWords : List (ℕ × String) :=
  [(1, "bbabaBabaBaBabaBabab"), (2, "abbabaBabbaBababbaBa"), (3, "BabbaBabaBaBabaBabaBaB")]

@[expose] def ruSzInvOK : Bool := invOK 4060 sTab sInv && invOK 4060 tTab tInv

@[expose] def ruSzRelsOK : Bool :=
  szRels.all fun v =>
    tblEq 4060 (CFSG.Sporadic.Bridge.TwoGen.Native.wordTab 4060 sTab sInv tTab tInv v) (idT 4060)

@[expose] def ruSzNontriv : Bool := !tblEq 4060 sTab (idT 4060)

@[expose] def ruSzNormOK : Bool :=
  normWords.all fun c => tblEq 4060 (conjTab c.1 (if c.2.1 then tTab else sTab)) (kTab c.2.2)

@[expose] def ruSzCentOK : Bool :=
  tblEq 4060 (compT 4060 bTab bTab) (idT 4060) && !tblEq 4060 bTab (idT 4060) &&
    !tblEq 4060 bTab (tblOfArr ruA0A) &&
    tblEq 4060 (compT 4060 bTab sTab) (compT 4060 sTab bTab) &&
    tblEq 4060 (compT 4060 bTab tTab) (compT 4060 tTab bTab)

@[expose] def ruSzFixOK : Bool :=
  let hT := hWords.map kTab
  hT.all (fun T => ap T 0 == 0) &&
    (List.range 4060).filter (fun x => hT.all fun T => ap T x == x) == [0, 1, 3645, 3692]

@[expose] def ruSzPtsOK : Bool := ptWords.all fun c => ap (kTab c.2) 0 == c.1

@[expose] def ruSzCheck : Bool :=
  ruSzInvOK && ruSzRelsOK && ruSzNontriv && ruSzNormOK && ruSzCentOK && ruSzFixOK && ruSzPtsOK

end CFSG.EvenSporadicStandard.Induction.RuSz
