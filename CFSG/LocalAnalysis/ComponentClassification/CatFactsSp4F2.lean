module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4F2Model
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4q
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3
public import Certificates.Certificate2007
public import Certificates.Certificate2012
public import Certificates.Certificate2013
public import Certificates.Certificate2014
public import Certificates.Certificate2015
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open CFSG Subgroup GSThmB

theorem cfSp4F2 : CFSp4F2 := by
  intro K₀ _ _ p f hp hp2 hf hK α hα Q hQC hQS
  have hfixeq : Eight.fixSubgroup α = fixOf α := by
    ext x
    rfl
  by_cases h5 : 5 ≤ p ^ f
  · rcases hK with hK | ⟨rfl, rfl, -⟩
    · exact f2_main hp hp2 hf h5 hK α hα.sq hα.out (hfixeq ▸ hα.dvd) Q hQC hQS
    · norm_num at h5
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hf1 : f = 1 := by
      by_contra hf1
      have h2f : 2 ≤ f := by omega
      have : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos h2f
      nlinarith
    subst hf1
    have hp3' : p = 3 := by
      rw [pow_one] at h5
      have hp5 : p < 5 := by omega
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    subst hp3'
    have hadm : Cat8.IsAdm K₀ α := ⟨hα.sq, hα.out, by simpa [Cat8.ordL2] using hα.dvd⟩
    have htop := CatFactsSmall.cfQ3Out K₀ hK α hadm
    have heq : (Cat8.Inn K₀ ⊔ zpowers α) ⊓ centralizer ({α} : Set (MulAut K₀)) =
        centralizer ({α} : Set (MulAut K₀)) := by
      rw [htop, top_inf_eq]
    rw [heq] at hQC hQS
    exact CatFactsSmall.cfQ3F2 K₀ hK α hadm Q hQC hQS

end CFSG.ComponentClassification.CatFactsSp4
