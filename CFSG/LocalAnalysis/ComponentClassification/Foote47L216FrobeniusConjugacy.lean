module


public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFixedBasis
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisGood
import CFSG.Assembly.ComponentTypeDefs

public section

open scoped MatrixGroups
open CFSG.GorensteinWalter
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartOne.KCRootAxis

namespace CFSG.ComponentClassification.Foote47L216

open CFSG.ComponentClassification.FixedCommutingProduct

abbrev F16L216 := GaloisField 2 4
abbrev S16L216 := PSL2 F16L216

@[expose] noncomputable def standardPhi : MulAut S16L216 :=
  psl2FieldAut F16L216 (iterateFrobeniusEquiv F16L216 2 2)

@[simp] theorem standardPhi_def :
    standardPhi = psl2FieldAut F16L216 (iterateFrobeniusEquiv F16L216 2 2) := rfl

end CFSG.ComponentClassification.Foote47L216
