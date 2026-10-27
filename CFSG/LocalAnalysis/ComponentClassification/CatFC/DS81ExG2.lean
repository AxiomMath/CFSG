module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTransport
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Ree.LargeReeEightTorus
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
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.Sporadic.Schreier.TitsOther
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

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog (g2c g2v even_G2_involutions_conjugate_to_root_elements)

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem isRoot_g2c_ex : IsRoot .G2 g2c :=
  (g2_root_certificate.1 g2c).2 (by decide)

theorem isRoot_g2v_ex : IsRoot .G2 g2v :=
  (g2_root_certificate.1 g2v).2 (by decide)

theorem g2_exists_order_eightynine_commute [Finite K] [CharP K 2] {ε : Kˣ} (hε : orderOf ε = 89) :
    ∀ y ∈ ([⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩,
        ⟨pinnedX .G2 K g2v 1, pinnedX_mem_adjointGroup g2v 1⟩] : List (adjointGroup .G2 K)),
      ∃ z : adjointGroup .G2 K, orderOf z = 89 ∧ Commute z y := by
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have h2 : ringChar K = 2 := ringChar.eq K 2
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · have hcomm := commute_rootDiagUnit_framePt (K := K) (τ := .G2) [g2c]
      (fun β hβ => by rw [List.mem_singleton.1 hβ]; exact isRoot_g2c_ex)
      (![3, -2] : Fin Tag.G2.rank → ℤ) (by decide) ε
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hcomm
    refine ⟨⟨rootDiagUnit .G2 fun i => ε ^ (![3, -2] : Fin Tag.G2.rank → ℤ) i,
      rootDiagUnit_mem_adjointGroup_of_charTwo (Or.inl rfl) h2 _⟩, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]
      exact orderOf_rootDiagUnit_eq_prime (τ := .G2) (K := K) hε (![3, -2] : Fin Tag.G2.rank → ℤ)
        ⟨0, by decide⟩ (by decide)
    · exact Subtype.ext hcomm.eq
  · have hcomm := commute_rootDiagUnit_framePt (K := K) (τ := .G2) [g2v]
      (fun β hβ => by rw [List.mem_singleton.1 hβ]; exact isRoot_g2v_ex)
      (![2, -1] : Fin Tag.G2.rank → ℤ) (by decide) ε
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hcomm
    refine ⟨⟨rootDiagUnit .G2 fun i => ε ^ (![2, -1] : Fin Tag.G2.rank → ℤ) i,
      rootDiagUnit_mem_adjointGroup_of_charTwo (Or.inl rfl) h2 _⟩, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]
      exact orderOf_rootDiagUnit_eq_prime (τ := .G2) (K := K) hε (![2, -1] : Fin Tag.G2.rank → ℤ)
        ⟨0, by decide⟩ (by decide)
    · exact Subtype.ext hcomm.eq

theorem lie23To89At_G2 : Lie23To89At .G2 := by
  intro X _ _ n f hadm hM τ hτ h23
  have hn : n = 0 := hadm.2.2.1
  subst hn
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hM.chevalleyExceptionalModel (by decide)
  have hK2 : ringChar K = 2 :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hadm.2.1 hcard
  haveI : CharP K 2 := ringChar.of_eq hK2
  have h11 : 11 ∣ f := eleven_dvd_of_twentythree_dvd_card (by simp) hadm hM
    (dvd_trans h23 (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨ε, hε⟩ := exists_unit_orderOf_eightynine_of_card hcard h11
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have hcov : ∀ x : adjointGroup .G2 K, x * x = 1 → x ≠ 1 →
      ∃ y ∈ ([⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩,
          ⟨pinnedX .G2 K g2v 1, pinnedX_mem_adjointGroup g2v 1⟩] : List (adjointGroup .G2 K)),
        IsConj y x := by
    intro x hx hx1
    have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx) hx1
    rcases even_G2_involutions_conjugate_to_root_elements K hK2 x hxo with h | h
    · exact ⟨⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩, by simp, h.symm⟩
    · exact ⟨⟨pinnedX .G2 K g2v 1, pinnedX_mem_adjointGroup g2v 1⟩, by simp, h.symm⟩
  exact prime_dvd_card_centralizer_of_classesCover (e.trans (adjointQuotientEquiv .G2 K))
    hcov (g2_exists_order_eightynine_commute hε) hτ

end CFSG.ComponentClassification.CatFC.DS81.Ex
