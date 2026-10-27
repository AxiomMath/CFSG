module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranch
public import CFSG.LocalAnalysis.QuasithinUnique.ComponentEmbeddingBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.GlueCat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.PositiveCore

public section

namespace CFSG.QuasithinUnique

open CFSG.QuasithinUnique.K1

theorem benderBranch_of_inputs
    (h1 : K1FamilyRecognition AltFamily) (h2 : K1FamilyRecognition OddClassicalFamily)
    (h3 : K1FamilyRecognition EvenClassicalFamily)
    (h4 : K1FamilyRecognition ExceptionalFamilyCat)
    (h5 : K1FamilyRecognition SmallLinearFamily) (h6 : K1FamilyRecognition SporadicFamilyCat) :
    BenderBranch :=
  have hrec := localComponentRecognition_of_families h1 h2 h3 h4 h5 h6
  benderBranch_of_interfaces hrec
    (componentEmbeddingUnderInvolution_of_localComponentRecognition hrec)

theorem constrainedBranch_of_inputs (hMB : MinParabolicBlocks)
    (hlin : Lin2BlockExcluded) (ha5 : A5BlockExcluded) (ha3 : SingleA3Excluded)
    (ha33 : DoubleA3Excluded) : ConstrainedBranch :=
  constrainedBranch_of_parts
    (constrainedSetup_of_blockProduction
      (blockProduction_of_minParabolicBlocks positiveTwoCoreSQTK hMB))
    hlin ha5 ha3 ha33

end CFSG.QuasithinUnique
