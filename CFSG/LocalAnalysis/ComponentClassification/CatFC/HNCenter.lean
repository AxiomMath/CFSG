module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HNFactsProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic
public import CFSG.Sporadic.HNOddCore.CTILocal
public import CFSG.Sporadic.HS
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
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
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ChainLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp31
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicSix
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicSix
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatOmegaMinusSporadic
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import Certificates.Certificate10027
public import Certificates.Certificate10095
public import Certificates.Certificate10095Base
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10104
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate2130
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate2323
public import Certificates.Certificate3085Base
public import Certificates.Certificate9201
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.RankThree.PartOne.HNRed
  CFSG.EvenSporadicStandard.TwoHS
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem eq_top_of_perfect_of_card_le_two_mul {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] {B : Subgroup E} (h : Nat.card E ≤ 2 * Nat.card B) : B = ⊤ := by
  have hidx : B.index * Nat.card B = Nat.card E := Subgroup.index_mul_card B
  have hle : B.index ≤ 2 := by
    by_contra hc
    have h3 : 3 ≤ B.index := by omega
    have := Nat.mul_le_mul_right (Nat.card B) h3
    have hpos : 0 < Nat.card B := Nat.card_pos
    omega
  have hnorm : B.Normal := by
    have hp : 0 < B.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rcases (by omega : B.index = 1 ∨ B.index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.1 h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  exact top_le_iff.1 (EvenSporadicStandard.Induction.Hyp.le_of_perfect_of_index_le_two hle
    inferInstance)

section HNCentre


theorem hn_six_component_center (B : Subgroup (Subgroup.centralizer {aJ} : Subgroup JH))
    (hB : CFSG.IsComponent B) : Nat.card (center B) = 2 := by
  have hd := coverData_aux t6C t6C_mem_ker t6C_ne_one t6C_central
  have hE := hd.isHSCover sign_core.2
  set E : Subgroup C6 := Dsub.comap phi6 with hEdef
  have hEn : E.Normal := hE.normal
  have hidx : E.index ≤ 2 := Nat.le_of_dvd (by norm_num) hE.index_dvd_two
  have hBE : B ≤ E := EvenSporadicStandard.Induction.Hyp.le_of_perfect_of_index_le_two hidx hB.1.1
  have hBq := cti_hn_six_pair_centralizer_component_simple_quotient_order B hB
  have hEq : Nat.card (E ⧸ center E) = 44352000 := by
    obtain ⟨f⟩ := hE.quotient
    rw [Nat.card_congr f.toEquiv]
    exact Sporadic.HS.card_HS
  have hEcard : Nat.card E = 2 * 44352000 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center E)
    rw [hEq, hE.card_center] at h
    omega
  have hBcard : 44352000 ≤ Nat.card B := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center B)
    rw [hBq] at h
    have hpos : 0 < Nat.card (center B) := Nat.card_pos
    omega
  have : Group.IsPerfect ↥E := hE.perfect
  have htop := eq_top_of_perfect_of_card_le_two_mul (E := ↥E) (B := B.subgroupOf E) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBE).toEquiv]
    omega)
  have hEB : E ≤ B := fun x hx => by
    have h := (top_le_iff.2 htop) (Subgroup.mem_top (⟨x, hx⟩ : ↥E))
    rwa [Subgroup.mem_subgroupOf] at h
  have hBeq : B = E := le_antisymm hBE hEB
  rw [hBeq]
  exact hE.card_center

theorem exists_component_centralizer_of_conj_center {S : Type} [Group S] (u : S)
    {D : Subgroup ↥(fixedSubgroup (MulAut.conj u))} (hD : IsComponent D) :
    ∃ B : Subgroup ↥(centralizer ({u} : Set S)), IsComponent B ∧
      Nat.card (center B) = Nat.card (center D) := by
  let φ := MulEquiv.subgroupCongr (SeitzReduction.F4Pilot.fixedSubgroup_conj u)
  exact ⟨D.map φ.toMonoidHom, ComponentClassification.CatLeaf.isComponent_map_mulEquiv φ hD,
    (Nat.card_congr (Subgroup.centerCongr
      (D.equivMapOfInjective φ.toMonoidHom φ.injective)).toEquiv).symm⟩

theorem exists_component_of_conj_center {S G0 : Type*} [Group S] [Group G0] {J : Subgroup G0}
    (f : S ≃* J) (a : S) (c g : J) (hg : g * c * g⁻¹ = f a)
    (B : Subgroup (Subgroup.centralizer ({a} : Set S))) (hB : CFSG.IsComponent B) :
    ∃ B' : Subgroup (Subgroup.centralizer ({c} : Set J)), CFSG.IsComponent B' ∧
      Nat.card (center B) = Nat.card (center B') := by
  have e2 : Subgroup.centralizer ({f a} : Set J) ≃* Subgroup.centralizer ({c} : Set J) :=
    (MulEquiv.subgroupCongr (show Subgroup.centralizer ({f a} : Set J) =
      Subgroup.centralizer {g * c * g⁻¹} by rw [hg])).trans
        (Sporadic.HNOddCore.centralizerConjEquiv c g).symm
  set ψ := (Sporadic.HNOddCore.centralizerMapEquiv f a).trans e2
  exact ⟨B.map ψ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv ψ hB,
    Nat.card_congr (Subgroup.centerCongr (B.equivMapOfInjective ψ.toMonoidHom ψ.injective)).toEquiv⟩

theorem hn_inner_component_center {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.HN) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hin : σ ∈ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) : Nat.card (center ↥D) = 2 := by
  obtain ⟨u, rfl⟩ := hin
  have hu : orderOf u = 2 := SeitzReduction.OmegaPilot.orderOf_eq_two_of_conj hS hna hσ
  obtain ⟨B, hB, hZ⟩ := exists_component_centralizer_of_conj_center u hD
  rw [← hZ]
  set f : S ≃* JH := e.trans hnEquivJ
  obtain ⟨h2, h1⟩ := map_involution f hu
  rcases isConj_aJ_or_t4J h2 h1 with hc | hc
  · obtain ⟨g, hg⟩ := sub_isConj_iff.1 hc
    obtain ⟨B', hB', hZ'⟩ := exists_component_of_conj_center f u aJ g hg B hB
    rw [hZ']
    exact hn_six_component_center B' hB'
  · obtain ⟨g, hg⟩ := sub_isConj_iff.1 hc
    obtain ⟨B', hB', -⟩ := exists_component_of_conj_center f u t4J g hg B hB
    exact absurd hB' (cti_hn_four_pair_centralizer_has_no_components.2 B')

end HNCentre

end CFSG.ComponentClassification.CatFC
