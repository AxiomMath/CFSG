module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Main
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUCl3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIU3Spor

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem gs82Step6ThreeInputA0_holds
    (hS : SchreierFor Blueprint.Catalog) (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) : GS82Step6ThreeInputA0 :=
  gs82Step6ThreeInputA0_of_classical_spor hS hCI hUc cfQPUJ6ThreeClassical_holds
    cfQPUJ6ThreeSpor_holds

end CFSG.ComponentClassification.GSThmB
