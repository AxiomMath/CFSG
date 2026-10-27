module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.OddFixData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.CoverData

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native (ap wordT)
open CFSG.EvenSporadicStandard.HSStd (factsTbl commPt commPt2)

@[expose] def s6WWord : List ℕ := [0, 0, 0, 0, 0]

@[expose] def s6WTab : Tab := wordTabS 3850 hsC1Tabs s6WWord

@[expose] def s6W2Tab : Tab := comp 3850 s6WTab s6WTab

@[expose] def s6W3Tab : Tab := comp 3850 s6W2Tab s6WTab

@[expose] def s6XWord : List ℕ := [0, 0, 0, 1, 0, 0, 1, 0, 1]

@[expose] def s6XTab : Tab := wordTabS 3850 hsC1Tabs s6XWord

@[expose] def s6IsW (z : Tab) : Bool :=
  z == idTab 3850 || z == s6WTab || z == s6W2Tab || z == s6W3Tab

@[expose] def s6StrongCheck (n : ℕ) (T : Array Tab) (w : Tab) (gs : Array Tab) : Bool :=
  T.all fun x => (!(gs.all (commPt n x)) || s6IsW x) &&
    (!(gs.all (commPt2 n w x)) || s6IsW (comp n w x))

@[expose] def s6WSq : Bool := s6W2Tab == natArr (hsCentTbl 5)

@[expose] def s6Strong : Bool :=
  s6StrongCheck 3850 hsC1Enum.tabs (natArr (factsTbl 0)) hsOdd1Tabs

@[expose] def s6XRel : Bool :=
  comp 3850 s6XTab s6XTab == idTab 3850 && comp 3850 s6XTab s6WTab == comp 3850 s6W3Tab s6XTab

@[expose] def fixTab (n : ℕ) (T : Tab) : ℕ := (List.range n).countP fun i => T[i]! == i

@[expose] def fixTbl (n : ℕ) (T : CFSG.Sporadic.Th.Native.Table) : ℕ :=
  (List.range n).countP fun i => ap T i == i

@[expose] def s6FixOK : Bool :=
  permOK 3850 (hsCentTbl 12) && (natArr (hsCentTbl 12)).size == 3850 &&
    fixTab 3850 (natArr (hsCentTbl 5)) == 170 && fixTab 3850 (natArr (hsCentTbl 12)) == 30 &&
    fixTab 3850 s6XTab == 170 && fixTab 3850 (comp 3850 s6XTab (natArr (hsCentTbl 5))) == 170 &&
    fixTab 3850 (comp 3850 s6XTab s6WTab) == 30

@[expose] def s6CWord : List ℤ := [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]

@[expose] def s6FixCoverOK : Bool :=
  fixTbl 3850 coverX == 170 && fixTbl 3850 (wordT 3850 coverGen s6CWord) == 30

@[expose] def s6Fix : Bool := s6FixOK && s6FixCoverOK

end CFSG.EvenSporadicStandard.TwoHS
