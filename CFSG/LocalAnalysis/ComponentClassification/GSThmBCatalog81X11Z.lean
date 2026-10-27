module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11K3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11V

public section

namespace CFSG.ComponentClassification.GSThmB

theorem gs81Exit11Input_of_rec
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hrec : CF81Exit11Recognition) : GS81Exit11Input :=
  fun I => gs81Exit11Input_of' hS hU hheld (gs81Step11Input I) hrec I

end CFSG.ComponentClassification.GSThmB
