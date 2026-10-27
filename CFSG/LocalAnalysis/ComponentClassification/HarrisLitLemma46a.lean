module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB51
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyElement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools
public import CFSG.ClassicalInvolution.LBalance.Proof.Tools
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
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
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKProper
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
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

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X]

theorem centralizer_zpowers_eq {G : Type*} [Group G] (g : G) :
    centralizer ((zpowers g : Subgroup G) : Set G) = centralizer {g} := by
  ext y
  rw [mem_centralizer_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hy
    exact (hy g (mem_zpowers g)).symm
  · intro hy x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute g y from hy.symm) n).eq

omit [Finite X] in
theorem map_subtype_centralizer {t β : X} (ht : t ∈ centralizer ({β} : Set X)) :
    (centralizer ({(⟨t, ht⟩ : ↥(centralizer ({β} : Set X)))} :
      Set ↥(centralizer ({β} : Set X)))).map
      (centralizer ({β} : Set X)).subtype = centralizer ({t} : Set X) ⊓ centralizer {β} := by
  ext y
  constructor
  · rintro ⟨y', hy', rfl⟩
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, y'.2⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy')
  · rintro ⟨hyt, hyβ⟩
    refine ⟨⟨y, hyβ⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
    exact mem_centralizer_singleton_iff.mp hyt

theorem layerIn_eq_of_normal {G : Type*} [Group G] [Finite G] {Y C : Subgroup G} (hYC : Y ≤ C)
    (hYn : (Y.subgroupOf C).Normal) (hle : GSThmB.layerIn C ≤ Y) :
    GSThmB.layerIn Y = GSThmB.layerIn C := by
  apply le_antisymm
  · refine map_le_iff_le_comap.mpr (sSup_le fun J hJ => ?_)
    intro x hx
    have hL : IsPComponent 2 ((J.map Y.subtype).subgroupOf Y) := by
      rwa [subgroupOf, comap_map_eq_self_of_injective Y.subtype_injective]
    have hLC := UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal (map_subtype_le J) hYC
      hYn.isSubnormal hL
    have hmem : (⟨x, hYC x.2⟩ : ↥C) ∈ (J.map Y.subtype).subgroupOf C := ⟨x, hx, rfl⟩
    exact ⟨⟨(x : G), hYC x.2⟩,
      (le_sSup (s := {L : Subgroup ↥C | IsPComponent 2 L}) hLC : _ ≤ pLayer ↥C 2) hmem, rfl⟩
  · refine map_le_iff_le_comap.mpr (sSup_le fun J hJ => ?_)
    intro x hx
    have hJY : J.map C.subtype ≤ Y := (map_mono (le_sSup hJ)).trans hle
    have hL : IsPComponent 2 ((J.map C.subtype).subgroupOf C) := by
      rwa [subgroupOf, comap_map_eq_self_of_injective C.subtype_injective]
    have hLY := UnbalancedCorr.isPComponent_subgroupOf_of_le hJY hYC hL
    have hxY : (x : G) ∈ Y := hJY ⟨x, hx, rfl⟩
    have hmem : (⟨x, hxY⟩ : ↥Y) ∈ (J.map C.subtype).subgroupOf Y := ⟨x, hx, rfl⟩
    exact ⟨⟨(x : G), hxY⟩,
      (le_sSup (s := {L : Subgroup ↥Y | IsPComponent 2 L}) hLY : _ ≤ pLayer ↥Y 2) hmem, rfl⟩

abbrev MBar (β : X) : Type :=
  ↥(centralizer ({β} : Set X)) ⧸ pPrimeCore 2 ↥(centralizer ({β} : Set X))

variable {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem t_mem_centralizer_beta (hσ : Setup42 h hS w z) (i j : ℕ) :
    t ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
  mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hσ.beta_mem_H i j)).symm

@[expose] def tBar (hσ : Setup42 h hS w z) (i j : ℕ) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
  QuotientGroup.mk ⟨t, hσ.t_mem_centralizer_beta i j⟩

@[expose] def KBar (L : Subgroup X) (β : X) : Subgroup (MBar β) :=
  ((centralizerResidual L β).subgroupOf (centralizer ({β} : Set X))).map
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X))))

omit [Finite X] in
theorem K_le_centralizer_beta (i j : ℕ) :
    centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
      centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
  centralizerResidual_le.trans inf_le_right

theorem layerIn_centralizer_t (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    GSThmB.layerIn (centralizer ({(⟨t, hσ.t_mem_centralizer_beta i j⟩ :
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))} :
          Set ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) =
      (centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).subgroupOf
        (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  have hker : ¬ 2 ∣ Nat.card M.subtype.ker := by
    rw [ker_subtype, card_bot]
    norm_num
  have h1 := GSThmB.OddQuot.map_layerIn M.subtype hker
    (centralizer ({(⟨t, hσ.t_mem_centralizer_beta i j⟩ : ↥M)} : Set ↥M))
  rw [map_subtype_centralizer] at h1
  have h2 : GSThmB.layerIn (centralizer ({t} : Set X) ⊓ centralizer {β}) =
      centralizerResidual L β := hσ.pLayer_M hFC hKC i j
  rw [h2] at h1
  rw [← h1, subgroupOf, comap_map_eq_self_of_injective M.subtype_injective]

theorem layerIn_centralizer_tBar (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    GSThmB.layerIn (centralizer ({hσ.tBar i j} :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) =
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set t' : ↥M := ⟨t, hσ.t_mem_centralizer_beta i j⟩ with ht'
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ¬ 2 ∣ Nat.card π.ker := GSThmB.OddQuot.not_two_dvd_card_ker
  have ht2 : IsPGroup 2 (zpowers t') := by
    have hd : orderOf t' ∣ 2 ^ 1 := by
      rw [pow_one, ← Subgroup.orderOf_coe, ht', h.config.orderOf_eq]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hC : (centralizer ({t'} : Set ↥M)).map π = centralizer ({π t'} : Set (↥M ⧸ _)) := by
    have h1 := GSThmB.OddQuot.map_inf_centralizer π ht2 (Y := ⊤) (fun _ _ => mem_normalizer_iff.mpr
      fun _ => by simp) (GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict π hker ⊤)
    rw [top_inf_eq, centralizer_zpowers_eq, map_top_of_surjective π hπs, top_inf_eq,
      MonoidHom.map_zpowers, centralizer_zpowers_eq] at h1
    exact h1
  change GSThmB.layerIn (centralizer ({π t'} : Set (↥M ⧸ pPrimeCore 2 ↥M))) =
    ((centralizerResidual L β).subgroupOf M).map π
  rw [← hC, ← GSThmB.OddQuot.map_layerIn π hker, hσ.layerIn_centralizer_t hFC hKC i j]

theorem centralizer_beta_ne_top [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≠ ⊤ := by
  intro htop
  have hβ1 : w ^ (orderOf w / 2) * t ^ i * z ^ j ≠ 1 := fun h1 =>
    hσ.rho_beta_ne_one i j (by
      rw [show (⟨_, hσ.beta_mem_H i j⟩ : ↥(centralizer ({t} : Set X))) = 1 from Subtype.ext h1,
        map_one])
  have hcen : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab ((mem_center_iff.mp (show a ∈ center X by rw [ht]; exact mem_top a) b).symm)
  apply hβ1
  have hmem : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ center X := by
    rw [mem_center_iff]
    intro g
    have : g ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
      rw [htop]
      exact mem_top g
    exact mem_centralizer_singleton_iff.mp this
  rwa [hcen, mem_bot] at hmem

theorem layerIn_layer_centralizer_tBar [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    GSThmB.layerIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer ({hσ.tBar i j} : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) =
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have ha1 := hσ.layerIn_centralizer_tBar hFC hKC i j
  have hKM : SectionRank.IsKGroupCat ↥(centralizer ({β} : Set X)) :=
    UnbalancedCorr.isKGroupCat_of_ne_top hK (hσ.centralizer_beta_ne_top hnonab i j)
  have hKMbar : SectionRank.IsKGroupCat (MBar β) :=
    GSThmB.OddQuot.isKGroupCat_of_surjective hKM _ (QuotientGroup.mk'_surjective _)
  have hSchM := GSThmB.schreierSections_of_isKGroupCat hSch hKMbar
  have ht2 : ∃ n : ℕ, hσ.tBar i j ^ 2 ^ n = 1 := by
    refine ⟨1, ?_⟩
    rw [pow_one]
    change (QuotientGroup.mk _ : MBar β) ^ 2 = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨t, hσ.t_mem_centralizer_beta i j⟩ : ↥(centralizer ({β} : Set X))) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← h.config.orderOf_eq, pow_orderOf_eq_one,
        Subgroup.coe_one])
    rw [this, QuotientGroup.mk_one]
  have hbal := LBalance.pLayer_centralizer_element_le hSchM ht2
  have hO : pPrimeCore 2 (MBar β) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  rw [ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot hO] at hbal
  change GSThmB.layerIn _ ≤ _ at hbal
  rw [ha1] at hbal
  have hlayer : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hKC' : KBar L β ≤ centralizer ({hσ.tBar i j} : Set (MBar β)) := by
    rw [← ha1]
    exact map_subtype_le _
  have hnorm : ((layer (MBar β) ⊓ centralizer ({hσ.tBar i j} : Set (MBar β))).subgroupOf
      (centralizer ({hσ.tBar i j} : Set (MBar β)))).Normal := by
    refine ⟨fun x hx c => ?_⟩
    exact ⟨hlayer.conj_mem _ hx.1 c, (centralizer _).mul_mem
      ((centralizer _).mul_mem c.2 hx.2) ((centralizer _).inv_mem c.2)⟩
  rw [layerIn_eq_of_normal inf_le_right hnorm (by rw [ha1]; exact le_inf hbal hKC'), ha1]

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
