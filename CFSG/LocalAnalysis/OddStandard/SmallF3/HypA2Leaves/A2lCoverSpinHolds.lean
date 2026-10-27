module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverO73
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverPlus43
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverMinus43

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ComponentClassification

theorem a2lCoverSpin_holds
    (hC : HypA2.ChevOddInChev2) : a2lCoverSpin :=
  ⟨a2lCoverO73_holds hC, a2lCoverPlus43_holds hC, a2lCoverMinus43_holds hC⟩

theorem a2l_coverDatum_holds
    (hGr : TBLit.GriessMultipliersOdd)
    (hC : HypA2.ChevOddInChev2) : HypA2.CoverDatum :=
  a2l_coverDatum_of_rows hGr hC (a2lCoverSpin_holds hC)

end CFSG.OddStandard.SmallF3.HypA2Leaves
