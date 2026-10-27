module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovStep

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup

theorem cf23CoverStep_of_inputs
    (hI : CF23InnerFusion) (hGA : TBLit.GriessMultipliersAllModels)
    (hSM : SporadicMultTwoPartInput) (hSO : SolMax.SuzOuterComponentsInput)
    (hL4 : CF23L4U4O8Comp) : CF23CoverStep :=
  fun H _ _ h hT hZK hJ =>
    Hyp52.fus23ConclW_of_fus23Concl (fus23Concl_of_cover hI hGA hSM hSO hL4 H h hT hZK hJ)

end CFSG.ComponentClassification.GSThmB.Cov
