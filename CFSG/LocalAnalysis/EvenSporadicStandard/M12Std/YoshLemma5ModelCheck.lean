module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelTransfer

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable

@[expose] def nEGens (α k : ℕ) : Array Table := (nGens α k).extract 0 6

@[expose] def eCT : Table := modelT 16 6 eGens [(0, true), (0, true)]

@[expose] def nCT (α k : ℕ) : Table := modelT 16 9 (nGens α k) [(0, true), (0, true)]

@[expose] def eModelCheck : Bool := normCenCheck 16 16 eGens eGens 128 128 eCT

@[expose] def nModelCheck (α k : ℕ) : Bool :=
  normCenCheck 16 16 (nGens α k) (nEGens α k) 3072 128 (nCT α k)

@[expose] def lemma5ModelCheck : Bool :=
  eModelCheck && [0, 1].all fun α => [0, 1].all fun k => nModelCheck α k

end CFSG.EvenSporadicStandard.M12Std.Yosh
