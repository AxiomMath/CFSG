module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdSectionStd
public import CFSG.LocalAnalysis.ComponentInitial.KProperSolvableOddQuotientLayer
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.Adapters.ProjectiveSpecialLinear
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import CFSG.Adapters.StatedPSLTwo
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

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.GSThmB
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor conjSub isComponent_conjSub)
open CFSG.LocalAnalysis.ComponentInitial
  (kProper_solvable_odd_quotient_ordinary_local_image_enters_two_layer)

theorem gsRestricted_psl_two {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (h : LieModel Y .PSL 2 p f) : GSRestricted Y :=
  Or.inl ⟨p, f, hp, hp2, hf, h5, h⟩

theorem gsRestricted_alternating {Y : Type} [Group Y] {n : ℕ} (hn : 7 ≤ n)
    (h : Nonempty (Y ≃* alternatingGroup (Fin n))) : GSRestricted Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨n, hn, h⟩))))))))))

theorem gsRestricted_psl_three_four {Y : Type} [Group Y] (h : LieModel Y .PSL 3 2 2) :
    GSRestricted Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem gsRestricted_of_smallSource {A : Type} [Group A] {J : Subgroup A} (hs : SmallSource J) :
    GSRestricted (J ⧸ center J) := by
  rcases hs with ⟨p, f, hp, hp2, hf, h5, hm, -⟩ | ⟨h7, -⟩ | h34
  · exact gsRestricted_psl_two hp hp2 hf h5 hm
  · exact gsRestricted_alternating le_rfl h7
  · exact gsRestricted_psl_three_four h34

theorem isSimpleGroup_of_lieModel_PSL_two {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSL 2 p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_psl_two h

theorem center_eq_pPrimeCore_of_isSimpleGroup {A : Type} [Group A] {J : Subgroup A}
    (hJ : IsQuasisimple J) (hs : IsSimpleGroup (J ⧸ pPrimeCore 2 J)) :
    center J = pPrimeCore 2 J := by
  have hne : pPrimeCore 2 J ≠ ⊤ := by
    intro h
    obtain ⟨x, y, hxy⟩ := hs.exists_pair_ne
    apply hxy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.eq, h]
    exact mem_top _
  have hle : pPrimeCore 2 J ≤ center J :=
    (LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hJ _).resolve_right hne
  have hq : IsQuasisimple (J ⧸ pPrimeCore 2 J) := by
    refine LieType.CurtisTits.isQuasisimple_of_surjective hJ (QuotientGroup.mk'_surjective _) ?_
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.mpr fun x _ => (QuotientGroup.eq_one_iff x).mp (hall x))
  exact LieType.CurtisTits.center_eq_of_isSimpleGroup_quotient _ hle hs
    (exists_mul_ne_of_isQuasisimple hq)

theorem smallSource_of_type {A : Type} [Group A] [Finite A] {J : Subgroup A}
    (hJ : IsQuasisimple J)
    (h : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∨
      Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) ∨
      LieModel (J ⧸ center J) .PSL 3 2 2) : SmallSource J := by
  have hodd : Odd (Nat.card (pPrimeCore 2 J)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rcases h with ⟨p, f, hp, hp2, hf, h5, hm⟩ | h7 | h34
  · have hc := center_eq_pPrimeCore_of_isSimpleGroup hJ (isSimpleGroup_of_lieModel_PSL_two hm)
    refine Or.inl ⟨p, f, hp, hp2, hf, h5, ?_, hc ▸ hodd⟩
    exact LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hc).symm hm
  · obtain ⟨e7⟩ := h7
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have hc := center_eq_pPrimeCore_of_isSimpleGroup hJ e7.isSimpleGroup
    exact Or.inr (Or.inl ⟨⟨(QuotientGroup.quotientMulEquivOfEq hc).trans e7⟩, hc ▸ hodd⟩)
  · exact Or.inr (Or.inr h34)

variable {H : Type} [Group H]

theorem kProper_of_isKGroupCat' (hK : SectionRank.IsKGroupCat H) :
    Assembly.KProper Catalog H :=
  CFSG.KCore.KGroupNonab.kProperNonab (CFSG.KCore.KGroupAllSimple.kGroupNonab hK)

theorem catalog_secImg_self (hK : SectionRank.IsKGroupCat H) {L : Subgroup H}
    (hL : IsQuasisimple L) : Catalog (secImg L L) := by
  have : IsSimpleGroup (L ⧸ center L) := hL.2.1
  exact SectionRank.catalog_of_mulEquiv secImgEquiv.symm (hK L (center L) this)

variable [Finite H]

theorem isComponent_of_isPComponent_two (hO : pPrimeCore 2 H = ⊥) {M : Subgroup H}
    (hM : IsPComponent 2 M) : IsComponent M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).1 hM
  have hcore : pPrimeCore 2 M = ⊥ := by
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs
    rw [hO, inf_bot_eq] at h1
    exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp h1
  refine ⟨?_, hs⟩
  have e : M ⧸ pPrimeCore 2 M ≃* M :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hq

theorem le_layer_of_isComponentOf_centralizer (hS : SchreierFor Catalog)
    (hK : SectionRank.IsKGroupCat H) (hO : pPrimeCore 2 H = ⊥) {t : H} (ht : orderOf t = 2)
    {J : Subgroup H} (hJ : Assembly.IsComponentOf J (centralizer ({t} : Set H))) :
    J ≤ layer H := by
  have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup H)) :=
    (MonoidHom.ker_eq_bot_iff _).1 (QuotientGroup.ker_mk' _)
  have himage : Assembly.IsComponentOf (J.map (QuotientGroup.mk' (⊥ : Subgroup H)))
      (centralizer ({QuotientGroup.mk' (⊥ : Subgroup H) t} : Set (H ⧸ (⊥ : Subgroup H)))) := by
    have h := (LocalAnalysis.ComponentInitial.isComponentOf_map_iff hinj).2 hJ
    rwa [LocalAnalysis.ComponentInitial.map_centralizer_singleton_of_injective hinj,
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), top_inf_eq] at h
  have hJp : Group.IsPerfect J := ((AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ.2.2).1
  have hJ2 : J ≤ CFSG.pLayer H 2 :=
    kProper_solvable_odd_quotient_ordinary_local_image_enters_two_layer
      hS (kProper_of_isKGroupCat' hK) ⊥ (by rw [Subgroup.card_bot]; exact odd_one) ht hJ.1 hJp
      himage
  exact hJ2.trans (sSup_le fun Q hQ => le_sSup (isComponent_of_isPComponent_two hO hQ))

theorem gsRestricted_of_invariant_component
    (hAS : AlmostSimpleRestricted fun Y _ => Catalog Y) (hK : SectionRank.IsKGroupCat H)
    {J : Subgroup H} (hJ : IsStandardSubgroup J) (hn : ¬ J.Normal) (hs : SmallSource J)
    {L : Subgroup H} (hL : IsComponent L) (hJL : J ≤ L) {t : H}
    (htJ : t ∈ centralizer (J : Set H)) (ht2 : orderOf t = 2) (htN : t ∈ secN L) :
    GSRestricted (L ⧸ center L) := by
  have hJL' : J ≠ L := fun h => not_isComponent hJ hn (h ▸ hL)
  have htL : t ∉ centralizer (L : Set H) := by
    intro htL
    refine hJL' (eq_of_le_normalizer hJ.1 hL.1 hJL fun l hl => ?_)
    apply centralizer_le_normalizer hJ htJ ht2
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp htL) l hl
  have hstd := isStandardSubgroup_secImg hJ hJL htN htJ ht2 htL
  have htb2 : orderOf (secπ L ⟨t, htN⟩) = 2 := orderOf_secπ_eq_two ht2 htL
  have htbJ : secπ L ⟨t, htN⟩ ∈ centralizer (secImg L J : Set (secN L ⧸ secD L)) :=
    secπ_mem_centralizer htJ
  have hcomp := isComponentOf_centralizer hstd htbJ htb2
  have hres := hAS (secN L ⧸ secD L) (secImg L L) (secImg_self_isSimpleGroup hL.1)
    (secImg_self_nonabelian hL.1)
    (centralizer_secImg_self (commutator_self_eq_of_isQuasisimple hL.1))
    (catalog_secImg_self hK hL.1) (catalog_secImg_self hK hL.1) (secπ L ⟨t, htN⟩) htb2
    (secImg L J) (secImg_mono hJL) (secImg_ne_secImg_self hJ.1 hL.1 hJL hJL') hcomp hstd
    (smallSource_secImg hJ.1 hJL hs)
  exact OddQuot.gsRestricted_of_mulEquiv secImgEquiv.symm hres

noncomputable def centralQuotientConjugateEquiv {K : Subgroup H} (hK : IsQuasisimple K) (g : H) :
    K ⧸ center K ≃* conjugate K g ⧸ center (conjugate K g) :=
  let e : K ≃* conjugate K g :=
    K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hK e.surjective (by
    intro x hx
    rw [MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hx
    rw [hx]
    exact one_mem _)

theorem restrictedStandard_of_almostSimple (hS : SchreierFor Catalog)
    (hAS : AlmostSimpleRestricted fun Y _ => Catalog Y) : RestrictedStandardInput := by
  intro H _ _ hK hO J hJ hn hsmall K hKc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : SmallSource J := smallSource_of_type hJ.1 hsmall
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (J : Set H)) 2
    (even_iff_two_dvd.mp hJ.2.1)
  set t : H := (t₀ : H) with htdef
  have htJ : t ∈ centralizer (J : Set H) := t₀.2
  have ht2 : orderOf t = 2 := by rw [htdef, Subgroup.orderOf_coe, ht₀]
  have ht' : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht2
  have hJt := isComponentOf_centralizer hJ htJ ht2
  have hJE := le_layer_of_isComponentOf_centralizer hS hK hO ht2 hJt
  obtain ⟨L, hL, hcase⟩ :=
    LocalAnalysis.ComponentInitial.involution_layer_component_orbit_location ht2 hJt hJE
  obtain ⟨g, hg⟩ := exists_conjugate_commutator_ne_bot hO hJ hn hKc
  have hK'c : IsComponent (conjugate K g) := isComponent_conjSub hKc g⁻¹
  refine OddQuot.gsRestricted_of_mulEquiv (centralQuotientConjugateEquiv hKc.1 g).symm ?_
  rcases hcase with ⟨hLt, hJL⟩ | ⟨hLt, hJset, -, ⟨eJL⟩, -⟩
  ·
    have hJL' : J ≤ L := hJL.1.trans inf_le_left
    have heq : conjugate K g = L := by
      rcases LocalCores.distinct_components_commute hK'c hL with h | h
      · exact h
      · exfalso
        apply hg
        rw [commutator_comm]
        exact le_bot_iff.mp (h ▸ commutator_mono le_rfl hJL')
    have htN : t ∈ secN L :=
      LocalAnalysis.ComponentInitial.mem_normalizer_of_conjSub_inv_le ht' hLt.le
    rw [heq]
    exact gsRestricted_of_invariant_component hAS hK hJ hn hs hL hJL' htJ ht2 htN
  ·
    have hLtc : IsComponent (conjSub t⁻¹ L) := isComponent_conjSub hL _
    have hJres : GSRestricted (L ⧸ center L) :=
      OddQuot.gsRestricted_of_mulEquiv eJL (gsRestricted_of_smallSource hs)
    rcases LocalCores.distinct_components_commute hK'c hL with h | h
    · rw [h]
      exact hJres
    rcases LocalCores.distinct_components_commute hK'c hLtc with h' | h'
    · rw [h']
      exact OddQuot.gsRestricted_of_mulEquiv (centralQuotientConjugateEquiv hL.1 t) hJres
    exfalso
    apply hg
    rw [commutator_eq_bot_iff_le_centralizer]
    intro j hj
    have hj' : j ∈ (J : Set H) := hj
    rw [hJset] at hj'
    obtain ⟨x, hx, rfl⟩ := hj'
    have hxc : x ∈ centralizer (conjugate K g : Set H) :=
      (commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact h)) hx
    have hxt : t⁻¹ * x * t ∈ centralizer (conjugate K g : Set H) := by
      refine (commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact h')) ?_
      exact ⟨x, hx, by simp⟩
    exact mul_mem hxc hxt

end CFSG.ComponentClassification.RestrictedStd
