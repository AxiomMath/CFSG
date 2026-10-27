module

public import CFSG.Sporadic.SmallOddCore.HSLocalCheckInputs
public import CFSG.Sporadic.SmallOddCore.HSCheckInputs

public section

namespace CFSG.EvenSporadicStandard.HSStd

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore

@[expose] def factsHex : String := include_str "HSFactsTbl.txt"

@[expose] def factsTbl (k : ℕ) : Table := hexT 3 3850 (3850 * k) factsHex

@[expose] def outerCommOK (z t : Table) : Bool :=
  permOK 3850 z && !hsSift z && hsSift (compT 3850 z hsOuterTbl) && commTT 3850 z t

@[expose] def commPt (n : ℕ) (x g : Tab) : Bool := allBelow n fun i => x[g[i]!]! == g[x[i]!]!

@[expose] def commPt2 (n : ℕ) (w x g : Tab) : Bool :=
  allBelow n fun i => w[x[g[i]!]!]! == g[w[x[i]!]!]!

@[expose] def sqPt (n : ℕ) (x : Tab) : Bool := allBelow n fun i => x[x[i]!]! == i

@[expose] def sqPt2 (n : ℕ) (w x : Tab) : Bool := allBelow n fun i => w[x[w[x[i]!]!]!]! == i

@[expose] def sqCheck (n : ℕ) (T : Array Tab) (w : Tab) (gs : Array Tab) : Bool :=
  T.all fun x => (!(gs.all (commPt n x)) || sqPt n x) &&
    (!(gs.all (commPt2 n w x)) || sqPt2 n w x)

@[expose] def tablesOK : Bool :=
  permOK 3850 hsOuterTbl && permOK 3850 (hsCentTbl 5) &&
    outerCommOK (factsTbl 0) (hsCentTbl 5) && permOK 3850 (factsTbl 1) && hsSift (factsTbl 1) &&
    (invTab 3850 (natArr (factsTbl 1))).size == 3850 &&
    comp 3850 (invTab 3850 (natArr (factsTbl 1))) (natArr (factsTbl 1)) == idTab 3850

@[expose] def u1OK : Bool := sqCheck 3850 hsC1Enum.tabs (natArr (factsTbl 0)) hsC1Tabs

@[expose] def oddA : Tab := wordTabS 3850 hsC2Tabs [2, 2]

@[expose] def oddB : Tab := wordTabS 3850 hsC2Tabs [1, 0]

@[expose] def hInvTab : Tab := invTab 3850 (natArr (factsTbl 1))

@[expose] def oddConj : Array Tab :=
  #[comp 3850 (comp 3850 hInvTab oddA) (natArr (factsTbl 1)),
    comp 3850 (comp 3850 hInvTab oddB) (natArr (factsTbl 1))]

@[expose] def u2bOK : Bool :=
  wordTabS 3850 #[oddA] (List.replicate 5 0) == idTab 3850 &&
    wordTabS 3850 #[oddB] (List.replicate 3 0) == idTab 3850 &&
    comp 3850 (comp 3850 hInvTab (wordTabS 3850 #[oddA, oddB] [1, 0, 1, 0]))
        (natArr (factsTbl 1)) == natArr (hsCentTbl 5) &&
    sqCheck 3850 hsC1Enum.tabs (natArr (factsTbl 0)) oddConj

@[expose] def hsT0Words : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0],
    [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0]]

@[expose] def hsT0Gens : Array Tab :=
  Array.ofFn (n := 3) fun j => wordTabS 3850 hsC1Tabs (hsT0Words.getD j.val [])

@[expose] def hsT0Enum : Enum := enumBFS 3850 hsT0Gens 512

@[expose] def t0OK : Bool :=
  enumOK 3850 hsT0Gens hsT0Enum && hsT0Enum.tabs.size == 512 &&
    hsT0Enum.tabs.contains (natArr (hsCentTbl 5)) &&
    (hsC1Enum.tabs.toList.filter (fun x => hsT0Gens.all (commPt 3850 x))).length == 2

@[expose] def hsPerfWords : List (List ℕ) :=
  [[0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 1, 0, 0, 1, 0, 0, 0]]

@[expose] def hsPerfGens : Array Tab :=
  Array.ofFn (n := 2) fun j => wordTabS 3850 hsC1Tabs (hsPerfWords.getD j.val [])

@[expose] def hsPerfComm : List (List ℕ × List ℕ) :=
  [([0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0]),
    ([0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0], [0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1])]

@[expose] def commRel (gs : Array Tab) (q : Tab) (X Y : List ℕ) : Bool :=
  comp 3850 (comp 3850 q (wordTabS 3850 gs Y)) (wordTabS 3850 gs X) ==
    comp 3850 (wordTabS 3850 gs X) (wordTabS 3850 gs Y)

@[expose] def perfOK : Bool :=
  allBelow 2 (fun i => commRel hsPerfGens hsPerfGens[i]! (hsPerfComm.getD i ([], [])).1
    (hsPerfComm.getD i ([], [])).2) &&
    wordTabS 3850 hsPerfGens (List.replicate 6 0) == natArr (hsCentTbl 5)

@[expose] def factsData : Bool := tablesOK && u1OK && u2bOK && t0OK && perfOK

end CFSG.EvenSporadicStandard.HSStd
