module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinFacts
public import CFSG.GH74.E2.FactsK
public import CFSG.GH74.Generic.GKFFinal
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

theorem smallTwinLeaf_of_parts
    (hL4 : SL4FrameOuterQ8Free) (hU4 : SU4FrameOuterQ8Free) (h2M12 : Twin2M12Leaf)
    (h2Sz8 : Twin2Sz8Leaf) (h2An : Twin2AnLeaf) : SmallTwinLeaf :=
  smallTwinLeaf_of_facts (GH74.Generic.genericKnownFacts_of_griess
    ComponentClassification.TBLit.griessMultipliersAllModels_holds) GH74.E2.e2ComponentFacts hL4 hU4
    h2M12 h2Sz8 h2An

end CFSG.ClassicalInvolution.Q3.TA3
