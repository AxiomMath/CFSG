module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import Certificates.Certificate2022
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.BorelTits.CompleteFlag
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
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
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

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open scoped commutatorElement

namespace L34R

theorem exists_mul_mem_centralizer {P : Type*} [Group P] [Finite P] {e : P}
    (he : e ∈ Open.fusionZStar P) (he2 : e ^ 2 = 1) (w : P) :
    ∃ n ∈ pPrimeCore 2 P, w * n ∈ centralizer ({e} : Set P) := by
  have heinv : e⁻¹ = e := by
    rw [inv_eq_iff_mul_eq_one, ← sq, he2]
  have hc : ∀ x, MulAut.conj e (MulAut.conj e x) = x := by
    intro x
    simp only [MulAut.conj_apply, heinv]
    rw [show e * (e * x * e) * e = (e * e) * x * (e * e) by group, ← sq, he2]
    group
  have hcN : ∀ n ∈ pPrimeCore 2 P, MulAut.conj e n ∈ pPrimeCore 2 P := fun n hn => by
    rw [MulAut.conj_apply]
    exact (inferInstance : (pPrimeCore 2 P).Normal).conj_mem n hn e
  have hodd : Odd (Nat.card (pPrimeCore 2 P)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hw : w⁻¹ * MulAut.conj e w ∈ pPrimeCore 2 P := by
    have h1 := inv_mem ((GSThmB.OddQuot.mem_fusionZStar_iff.mp he) w⁻¹)
    rw [MulAut.conj_apply]
    convert h1 using 1
    rw [commutatorElement_def]
    group
  obtain ⟨n, hn, hfix⟩ := GrSLit.exists_fixed_mul_of_inv_mul_mem (MulAut.conj e) hc hcN hodd hw
  refine ⟨n, hn, ?_⟩
  rw [mem_centralizer_singleton_iff]
  rw [MulAut.conj_apply] at hfix
  calc w * n * e = e * (w * n) * e⁻¹ * e := by rw [hfix]
    _ = e * (w * n) := by group

theorem exists_involution_dvd_card_centralizer
    {Q : Type} [Group Q] [Finite Q] (hZ : Nat.card (center Q) ≤ 2) {P : Subgroup Q}
    (htype : IsL34Type (P ⧸ Open.fusionZStar P))
    (hrank : 2 ≤ pRank 2 ↥(Open.fusionZStar P)) :
    ∃ w : Q ⧸ center Q, orderOf w = 2 ∧
      20160 ∣ Nat.card (centralizer ({w} : Set (Q ⧸ center Q))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hA4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank hrank
  set ι : ↥(Open.fusionZStar P) →* Q := P.subtype.comp (Open.fusionZStar P).subtype with hιdef
  have hι : Function.Injective ι :=
    P.subtype_injective.comp (Open.fusionZStar P).subtype_injective
  obtain ⟨a, haA, hac⟩ : ∃ a ∈ A, ι a ∉ center Q := by
    by_contra h
    have hle : A.map ι ≤ center Q := by
      rintro _ ⟨a, ha, rfl⟩
      by_contra hn
      exact h ⟨a, ha, hn⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective hι, hA4] at h1
    omega
  set p₀ : ↥P := (a : ↥P) with hp₀def
  have hp₀ : p₀ ∈ Open.fusionZStar P := a.2
  have ha2 : a ^ 2 = 1 := hA.2 a haA
  have hp₀2 : p₀ ^ 2 = 1 := by
    have := congrArg (fun x : ↥(Open.fusionZStar P) => (x : ↥P)) ha2
    simpa [hp₀def] using this
  set e : Q := (p₀ : Q) with hedef
  have hιa : ι a = e := rfl
  have he2 : e ^ 2 = 1 := by
    have := congrArg (fun x : ↥P => (x : Q)) hp₀2
    simpa [hedef] using this
  set w : Q ⧸ center Q := QuotientGroup.mk' (center Q) e with hwdef
  have hw1 : w ≠ 1 := fun h => hac (by rw [hιa]; exact (QuotientGroup.eq_one_iff e).mp h)
  have hw2 : orderOf w = 2 :=
    orderOf_eq_prime (by rw [hwdef, ← map_pow, he2, map_one]) hw1
  refine ⟨w, hw2, ?_⟩
  set H : Subgroup ↥P := centralizer ({p₀} : Set ↥P) with hHdef
  set f₁ : ↥H →* Q ⧸ center Q :=
    (QuotientGroup.mk' (center Q)).comp (P.subtype.comp H.subtype) with hf₁def
  set f₂ : ↥H →* ↥P ⧸ Open.fusionZStar P :=
    (QuotientGroup.mk' (Open.fusionZStar P)).comp H.subtype with hf₂def
  have hOZ : ∀ n ∈ pPrimeCore 2 ↥P, n ∈ Open.fusionZStar P := fun n hn => by
    refine GSThmB.OddQuot.mem_fusionZStar_iff.mpr fun m => ?_
    rw [commutatorElement_def, show n * m * n⁻¹ * m⁻¹ = n * (m * n⁻¹ * m⁻¹) by group]
    exact mul_mem hn ((inferInstance : (pPrimeCore 2 ↥P).Normal).conj_mem _ (inv_mem hn) m)
  have hf₂ : Function.Surjective f₂ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Open.fusionZStar P) y
    obtain ⟨n, hn, hxn⟩ := exists_mul_mem_centralizer hp₀ hp₀2 x
    refine ⟨⟨x * n, hxn⟩, ?_⟩
    simp only [hf₂def, MonoidHom.coe_comp, Function.comp_apply, coe_subtype, map_mul,
      QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr (hOZ n hn), mul_one]
  have hker : f₁.ker ≤ f₂.ker := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh ⊢
    have hc : ((h : ↥P) : Q) ∈ center Q := by
      simp only [hf₁def, MonoidHom.coe_comp, Function.comp_apply, coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hh
      exact hh
    refine (QuotientGroup.eq_one_iff _).mpr (GSThmB.OddQuot.mem_fusionZStar_iff.mpr fun m => ?_)
    have hcomm : (h : ↥P) * m = m * (h : ↥P) := by
      apply Subtype.ext
      exact (mem_center_iff.mp hc (m : Q)).symm
    rw [commutatorElement_def, coe_subtype, hcomm, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hrange : f₁.range ≤ centralizer ({w} : Set (Q ⧸ center Q)) := by
    rintro _ ⟨h, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hh : (h : ↥P) * p₀ = p₀ * (h : ↥P) := mem_centralizer_singleton_iff.mp h.2
    have hh' : ((h : ↥P) : Q) * e = e * ((h : ↥P) : Q) := by
      have := congrArg (fun x : ↥P => (x : Q)) hh
      simpa [hedef] using this
    simp only [hf₁def, hwdef, MonoidHom.coe_comp, Function.comp_apply, coe_subtype]
    rw [← map_mul, ← map_mul, hh']
  have hdvd : Nat.card (↥P ⧸ Open.fusionZStar P) ∣ Nat.card f₁.range := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hker
    have h1 := Subgroup.card_ker_mul_card_range f₁
    have h2 := Subgroup.card_ker_mul_card_of_surjective hf₂
    rw [hm] at h2
    have hpos : 0 < Nat.card f₁.ker := Nat.card_pos
    refine ⟨m, Nat.eq_of_mul_eq_mul_left hpos ?_⟩
    rw [h1, ← h2]
    ring
  rw [CatLeaf.card_of_isL34Type htype] at hdvd
  exact hdvd.trans (Subgroup.card_dvd_of_le hrange)

end L34R

end CFSG.ComponentClassification.GrSLit
