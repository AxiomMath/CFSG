module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldSupport
public import CFSG.LocalAnalysis.ComponentClassification.KProperComponentLocalBOpen

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34FieldCoreOfSignalizer_of_catalog
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) :
    L34FieldCoreOfSignalizer :=
  l34FieldCoreOfSignalizer_of_parts hS hU KProperRelativeB.heldInput
    (l34ActiveComponentBound_of_parts l34ActiveImageBound_holds l34ActiveSupportCount_holds)
    l3TwoPowChiefFixedPoints_holds

end CFSG.ComponentClassification.GrSLit.L34Sec5S
