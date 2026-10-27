module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Trans
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Ree.SuzukiSimple
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
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
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
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem inf_centralizer_subgroupOf {L : Subgroup X} {t : X} (htL : t ∈ L) :
    (L ⊓ centralizer ({t} : Set X)).subgroupOf L = centralizer ({⟨t, htL⟩} : Set ↥L) := by
  ext w
  rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun h => Subtype.ext h.2, fun h => ⟨w.2, congrArg Subtype.val h⟩⟩

theorem orderOf_mk_eq_two {G : Type} [Group G] [Finite G] {t : G} (ht : t * t = 1)
    (ht1 : t ≠ 1) : orderOf (QuotientGroup.mk' (pPrimeCore 2 G) t) = 2 := by
  refine orderOf_eq_prime (by rw [pow_two, ← map_mul, ht, map_one]) fun h1 => ?_
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two, ht]) ht1
  have hdvd : orderOf (⟨t, h1⟩ : pPrimeCore 2 G) ∣ Nat.card (pPrimeCore 2 G) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hto] at hdvd
  exact absurd (Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card) (by norm_num)

theorem exists_swap_of_cf (hCF : CFSp4Conj) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {L J₀ Y : Subgroup X} (hLie : Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSp 2 p f)
    {t w : X} (htL : t ∈ L) (ht : t * t = 1) (ht1 : t ≠ 1) (hw : w * w = 1) (hw1 : w ≠ 1)
    (htw : t * w = w * t) (hJ0L : J₀ ≤ L) (hJ0t : J₀ ≤ centralizer ({t} : Set X))
    (hYt : L ⊓ centralizer ({t} : Set X) ≤ Y) (hJ0pc : IsPComponent 2 (J₀.subgroupOf Y))
    (hwJ0 : w ∈ J₀) : ∃ r ∈ L, r * r = 1 ∧ r⁻¹ * t * r = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : ↥L := ⟨t, htL⟩ with ht'
  set w' : ↥L := ⟨w, hJ0L hwJ0⟩ with hw'
  have ht'2 : t' * t' = 1 := Subtype.ext ht
  have hw'2 : w' * w' = 1 := Subtype.ext hw
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hw'1 : w' ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have htw' : t' * w' = w' * t' := Subtype.ext htw
  have hJ0Lt : J₀ ≤ L ⊓ centralizer ({t} : Set X) := le_inf hJ0L hJ0t
  have hpc1 : IsPComponent 2 (J₀.subgroupOf (L ⊓ centralizer ({t} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0Lt hYt hJ0pc
  have hpc2 : IsPComponent 2 ((J₀.subgroupOf L).subgroupOf (centralizer ({t'} : Set ↥L))) := by
    rw [← inf_centralizer_subgroupOf htL]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hpc1
  have hMt : J₀.subgroupOf L ≤ centralizer ({t'} : Set ↥L) := by
    rw [← inf_centralizer_subgroupOf htL]
    intro v hv
    exact mem_subgroupOf.mpr (hJ0Lt (mem_subgroupOf.mp hv))
  obtain ⟨hMbt, hMbpc⟩ := isPComponent_centralizer_map ht'2 hMt hpc2
  obtain ⟨rb, hrb, hrbt⟩ := hCF _ p f hp hp2 hf hLie _ _ (orderOf_mk_eq_two ht'2 ht'1)
    (orderOf_mk_eq_two hw'2 hw'1) _ hMbt hMbpc (mem_map_of_mem _ (mem_subgroupOf.mpr hwJ0))
  obtain ⟨r, hr, hrt⟩ := lift_swap ht'2 hw'2 htw' hrb hrbt
  exact ⟨r, r.2, congrArg Subtype.val hr, congrArg Subtype.val hrt⟩

end Seven

end CFSG.ComponentClassification.GSThmB
