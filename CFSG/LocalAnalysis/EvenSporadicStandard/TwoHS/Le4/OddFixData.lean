module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsData

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.HSStd (factsTbl commPt commPt2 sqPt)

@[expose] def hsOdd1WordA : List ℕ := [0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0]

@[expose] def hsOdd1WordB : List ℕ := [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0]

@[expose] def hsOdd1TabA : Tab := wordTabS 3850 hsC1Tabs hsOdd1WordA

@[expose] def hsOdd1TabB : Tab := wordTabS 3850 hsC1Tabs hsOdd1WordB

@[expose] def hsOdd1Tabs : Array Tab := #[hsOdd1TabA, hsOdd1TabB]

@[expose] def hsOdd1TabAB : Tab := comp 3850 hsOdd1TabA hsOdd1TabB

@[expose] def quartPt (n : ℕ) (x : Tab) : Bool := sqPt n (comp n x x)

@[expose] def quartPt2 (n : ℕ) (w x : Tab) : Bool := sqPt n (comp n (comp n w x) (comp n w x))

@[expose] def quartCheck (n : ℕ) (T : Array Tab) (w : Tab) (gs : Array Tab) : Bool :=
  T.all fun x => (!(gs.all (commPt n x)) || quartPt n x) &&
    (!(gs.all (commPt2 n w x)) || quartPt2 n w x)

@[expose] def hsOdd1PowA : Bool := wordTabS 3850 #[hsOdd1TabA] (List.replicate 5 0) == idTab 3850

@[expose] def hsOdd1PowB : Bool := wordTabS 3850 #[hsOdd1TabB] (List.replicate 5 0) == idTab 3850

@[expose] def hsOdd1PowAB : Bool :=
  wordTabS 3850 #[hsOdd1TabAB] (List.replicate 10 0) == natArr (hsCentTbl 5)

@[expose] def hsOdd1Quart : Bool :=
  quartCheck 3850 hsC1Enum.tabs (natArr (factsTbl 0)) hsOdd1Tabs

end CFSG.EvenSporadicStandard.TwoHS
