module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcL2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcG23Holds

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ComponentClassification

theorem a2l_chev3Exceptions_of_inputs (hGr : TBLit.GriessMultipliersOdd)
    (hCL2 : HypA2.ClosureFieldExp) (hQ : a2lFixedQuasi) (hG : a2lG23Comp) :
    a2lChev3Exceptions :=
  ⟨a2l_chev3On_l2 hGr hCL2, a2l_chev3On_g23 hQ hG, a2l_chev3On_ree hCL2 hQ⟩

section Holds


theorem a2l_chev3Exceptions_holds (hGr : TBLit.GriessMultipliersOdd)
    (hCL2 : HypA2.ClosureFieldExp) : a2lChev3Exceptions :=
  a2l_chev3Exceptions_of_inputs hGr hCL2 a2lFixedQuasi_holds a2lG23Comp_holds

end Holds

end CFSG.OddStandard.SmallF3.HypA2Leaves
