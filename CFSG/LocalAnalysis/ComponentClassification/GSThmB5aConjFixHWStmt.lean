module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFixHW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypesHW

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedCorr

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor) in
theorem conjFixStatementHW_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput) :
    ConjFixStatementHW :=
  fun _ _ _ h _ hg he hP => h.conj_fix hS hU hheld hg he hP

end CFSG.ComponentClassification.GSThmB
