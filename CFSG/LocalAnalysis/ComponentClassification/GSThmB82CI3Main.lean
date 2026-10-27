module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Glue
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Rows
public import CFSG.LieType.Ree.SmallReeInvolutionComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTrialityInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Inner
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2QPU
public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6Graph
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem gs82Step6ThreeInputA0_of_classical_spor
    (hS : SchreierFor Blueprint.Catalog) (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hC : CFQPUJ6ThreeClassical)
    (hSp : CFQPUJ6ThreeSpor) : GS82Step6ThreeInputA0 :=
  gs82Step6ThreeInputA0_of_catalog hS hCI hUc (cfQPUJ6Three_of_classical_spor hC hSp)

end CFSG.ComponentClassification.GSThmB
