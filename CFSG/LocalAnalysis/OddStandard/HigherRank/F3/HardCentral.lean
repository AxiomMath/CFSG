module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.HarrisLit

private theorem pPrimeCore_ne_top_of_involution {Q : Type*} [Group Q] [Finite Q] {y : Q}
    (hy : orderOf y = 2) : pPrimeCore 2 Q ≠ ⊤ := by
  intro h
  have hyO : y ∈ pPrimeCore 2 Q := by rw [h]; exact Subgroup.mem_top y
  have hdvd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 Q) hyO
  rw [hy] at hdvd
  exact absurd hdvd
    (Nat.prime_two.coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (p := 2) (G := Q)))

theorem mem_center_of_map_mem_center {A B : Type*} [Group A] [Group B] (hA : IsQuasisimple A)
    (f : A →* B) (hker : f.ker ≤ center A) {x : A} (hx : f x ∈ center B) : x ∈ center A := by
  have hfr : (f.rangeRestrict).ker ≤ center A := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker
  rw [← LocalCores.comap_center_eq_of_perfect hA.1 f.rangeRestrict
    f.rangeRestrict_surjective hfr, Subgroup.mem_comap]
  refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
  obtain ⟨a, ha⟩ := g.2
  show (g : B) * f x = f x * (g : B)
  rw [← ha]
  exact Subgroup.mem_center_iff.mp hx (f a)

theorem isQuasisimple_of_central_ker {A B : Type*} [Group A] [Group B] (hA : IsQuasisimple A)
    (f : A →* B) (hf : Function.Surjective f) (hker : f.ker ≤ center A) : IsQuasisimple B :=
  LocalCores.isQuasisimple_of_surjective hA f hf hker

theorem nonempty_quotCenter_equiv_of_central_ker {A B : Type*} [Group A] [Group B]
    (hA : IsQuasisimple A) (f : A →* B) (hf : Function.Surjective f) (hker : f.ker ≤ center A) :
    Nonempty (A ⧸ center A ≃* B ⧸ center B) := by
  have hc : center A = ((QuotientGroup.mk' (center B)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      LocalCores.comap_center_eq_of_perfect hA.1 f hf hker]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

theorem lieModel_quotCenter_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {τ : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : Blueprint.LieModel (A ⧸ center A) τ n p f) :
    Blueprint.LieModel (B ⧸ center B) τ n p f :=
  GSThmB.OddQuot.lieModel_of_equiv
    (QuotientGroup.congr _ _ e (OuterAutomorphisms.center_map_equiv e)) h

theorem isTwoQuasisimple_of_involution {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    {y : Q} (hy : orderOf y = 2) : IsTwoQuasisimple Q := by
  have hOn : pPrimeCore 2 Q ≠ ⊤ := pPrimeCore_ne_top_of_involution hy
  have hOc : pPrimeCore 2 Q ≤ center Q :=
    (LocalCores.quasisimple_normal_subgroups hQ inferInstance).resolve_left hOn
  exact ⟨hQ.1, (LocalCores.quasisimple_central_quotient hQ (pPrimeCore 2 Q) hOc).1⟩

theorem fusionZStar_eq_center_of_involution {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) {y : Q} (hy : orderOf y = 2) : Open.fusionZStar Q = center Q :=
  CatLeaf.fusionZStar_eq_center_of_quasisimple hQ (pPrimeCore_ne_top_of_involution hy)

end CFSG.OddStandard.HigherRank.F3
