module

public import CFSG.LieType.ChevTwo.OrthogonalBasic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
import CFSG.ClassicalInvolution.ModelFacts.OrthAutSim
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

namespace CFSG.LieType.ChevTwo

open CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy
open CFSG.ClassicalInvolution.ModelFacts.OrthAut
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LieType.Universal.Spin
open scoped Pointwise

local notation "Q8" => StatedQuadPlus 4 (ZMod 2)
local notation "Ω8" => StatedOmega (StatedQuadPlus 4 (ZMod 2))
local notation "P8" => StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2)))

namespace AutEight

theorem statedScalars_eq_bot : StatedScalars (Fin 4 ⊕ Fin 4) (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  have hc : c = 1 := by revert c; decide
  rw [hc, map_one]
  exact Subgroup.one_mem _

theorem mk_injective :
    Function.Injective (QuotientGroup.mk'
      ((StatedScalars (Fin 4 ⊕ Fin 4) (ZMod 2)).subgroupOf Ω8)) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', statedScalars_eq_bot,
    Subgroup.bot_subgroupOf]

noncomputable def projEquiv : Ω8 ≃* P8 :=
  MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨mk_injective, QuotientGroup.mk'_surjective _⟩

theorem projEquiv_apply (x : Ω8) : projEquiv x = QuotientGroup.mk' _ x := rfl

theorem zmodTwo_ringEquiv_apply (σ : ZMod 2 ≃+* ZMod 2) (x : ZMod 2) : σ x = x := by
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h x with rfl | rfl
  · exact map_zero σ
  · exact map_one σ

theorem inducedByIso_of_smul_eq (α : MulAut Ω8)
    (hα : MulAut.congr projEquiv α • statedPointFamily (coe_quadPlus 4 (ZMod 2)) =
      statedPointFamily (coe_quadPlus 4 (ZMod 2))) :
    InducedByIso Q8 α := by
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hadm : StatedLieAdmissible .POmegaPlus 4 2 1 := ⟨Nat.prime_two, le_rfl, le_rfl⟩
  have h : StatedClassicalModel P8 .POmegaPlus 4 2 1 :=
    ⟨hadm, ZMod 2, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hmem := congr_mem_pointFamilyAut _ hα
  rw [coordinate_plus_family_eq_matrixImage h (ZMod 2) hK (MulEquiv.refl _)] at hmem
  obtain ⟨A, σ, μ, hQ, hx⟩ := exists_similarity_of_mem_image (plusIndexEquiv 4)
    (quadPlus 4 (ZMod 2)) (coe_quadPlus 4 (ZMod 2)) _ hmem
  have hσ : ∀ x, σ x = x := zmodTwo_ringEquiv_apply σ
  have hμ : μ = 1 := Subsingleton.elim _ _
  have hgl : ∀ g : GL (Fin 4 ⊕ Fin 4) (ZMod 2),
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv _ σ g = g := by
    intro g
    apply Units.ext
    ext i j
    exact hσ _
  refine ⟨A, fun v => ?_, fun x => ?_⟩
  · have := hQ v
    simp only [hσ, hμ, Units.val_one, one_mul, coe_quadPlus] at this
    exact this
  · obtain ⟨y, hy, hxy⟩ := hx x
    have h0 : (MulAut.congr projEquiv α) (QuotientGroup.mk x) = projEquiv (α x) := by
      change (MulAut.congr projEquiv α) (projEquiv x) = _
      simp [MulAut.congr_apply]
    have h1 : α x = y := projEquiv.injective (h0.symm.trans hxy)
    rw [h1, hy, hgl]

theorem exists_conj_smul_eq_of_odd {A X : Type*} [Group A] [MulAction A X] {x : X}
    (hodd : ¬ 2 ∣ Nat.card (MulAction.orbit A x)) {T : Subgroup A} (hT : IsPGroup 2 T) :
    ∃ g : A, ∀ t ∈ T, (g⁻¹ * t * g) • x = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨y, hy⟩, hfix⟩ :=
    hT.nonempty_fixed_point_of_prime_not_dvd_card (MulAction.orbit A x) hodd
  obtain ⟨g, rfl⟩ := hy
  refine ⟨g, fun t ht => ?_⟩
  have h2 : t • g • x = g • x := congrArg Subtype.val (hfix ⟨t, ht⟩)
  rw [mul_smul, mul_smul, h2, inv_smul_smul]

theorem plusSwapMatrix_mem_isoGrp :
    plusSwapMatrix 4 (ZMod 2) (by norm_num) ∈ isoGrp Q8 :=
  statedQuadPlus_plusSwapMatrix_mulVec 4 (ZMod 2) (by norm_num)

theorem congr_kappa_swap :
    MulAut.congr projEquiv (kappa Q8 ⟨_, plusSwapMatrix_mem_isoGrp⟩) =
      plusSwapAut 4 (ZMod 2) (by norm_num) := by
  ext p
  obtain ⟨x, rfl⟩ := projEquiv.surjective p
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    projEquiv_apply, projEquiv_apply, plusSwapAut_mk]
  exact congrArg (QuotientGroup.mk' _)
    (Subtype.ext (by rw [kappa_apply_val, plusSwapDerived_val]))

theorem congr_kappa_inner (w : Ω8) :
    MulAut.congr projEquiv (kappa Q8 ⟨w, statedOmega_le_isoGrp _ w.2⟩) =
      MulAut.conj (projEquiv w) := by
  ext p
  obtain ⟨x, rfl⟩ := projEquiv.surjective p
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg projEquiv (Subtype.ext (by rw [kappa_apply_val]; simp))

theorem conj_smul_conjugacyFamily {G : Type*} [Group G] (c : G) (H : Subgroup G) :
    MulAut.conj c • conjugacyFamily H = conjugacyFamily H := by
  have hc : ∀ g : G, (H.map (MulAut.conj c).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      H.map (MulAut.conj (g * c)).toMonoidHom := by
    intro g
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  rw [conjugacyFamily_covariance]
  ext U
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g * c, (hc g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * c⁻¹, (hc (g * c⁻¹)).trans (by rw [inv_mul_cancel_right])⟩

end AutEight

open AutEight

public section

theorem fix_plusEight
    (T : Subgroup (MulAut ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))))) (hT : IsPGroup 2 T) :
    ∃ τ : MulAut ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))),
      ∀ t ∈ T, InducedByIso (StatedQuadPlus 4 (ZMod 2)) (τ * t * τ⁻¹) := by
  set c := MulAut.congr projEquiv
  have hO := stated_pointFamily_orbit_subset (K := ZMod 2) (n := 4) rfl
  have hodd : ¬ 2 ∣ Nat.card (MulAction.orbit
      (MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2)))))
      (statedPointFamily (coe_quadPlus 4 (ZMod 2)))) := by
    rcases statedPointFamily_orbit_card 4 (ZMod 2) (by norm_num) hO with h | h <;> rw [h] <;>
      decide
  obtain ⟨γ, hγ⟩ := exists_conj_smul_eq_of_odd hodd (hT.map c.toMonoidHom)
  refine ⟨c.symm γ⁻¹, fun t ht => inducedByIso_of_smul_eq _ ?_⟩
  have hc : c (c.symm γ⁻¹ * t * (c.symm γ⁻¹)⁻¹) = γ⁻¹ * c t * γ := by
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
  rw [hc]
  exact hγ (c t) (Subgroup.mem_map_of_mem _ ht)

theorem commute_plusEight {g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)}
    (hg : g ∈ isoGrp (StatedQuadPlus 4 (ZMod 2))) (hgΩ : g ∉ StatedOmega (StatedQuadPlus 4 (ZMod 2)))
    (a : MulAut ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))))
    (h : a * kappa (StatedQuadPlus 4 (ZMod 2)) ⟨g, hg⟩ = kappa (StatedQuadPlus 4 (ZMod 2)) ⟨g, hg⟩ * a) :
    InducedByIso (StatedQuadPlus 4 (ZMod 2)) a := by
  set c := MulAut.congr projEquiv
  set s := plusSwapMatrix 4 (ZMod 2) (by norm_num)
  set F := statedPointFamily (coe_quadPlus 4 (ZMod 2))
  set CX := conjugacyFamily (statedProjectiveSubspaceStabilizer Q8 (flag 4 (ZMod 2) 4))
  set CXs := conjugacyFamily
    (statedProjectiveSubspaceStabilizer Q8 (Xstar 4 (ZMod 2) (by norm_num)))
  have hs : s ∈ isoGrp Q8 := plusSwapMatrix_mem_isoGrp
  have hne : CX ≠ CXs := conjugacyFamily_flag_ne_Xstar 4 (ZMod 2) (by norm_num)
  have hsΩ : s ∉ StatedOmega Q8 := by
    intro hsΩ
    have h1 := congr_kappa_inner ⟨s, hsΩ⟩
    rw [show (⟨(⟨s, hsΩ⟩ : StatedOmega Q8), statedOmega_le_isoGrp _ hsΩ⟩ : isoGrp Q8) = ⟨s, hs⟩
      from rfl, congr_kappa_swap] at h1
    have h2 := plusSwapAut_smul_conjugacyFamily_flag 4 (ZMod 2) (by norm_num)
    rw [h1, conj_smul_conjugacyFamily] at h2
    exact hne h2
  have hidx : ((StatedOmega Q8).subgroupOf (isoGrp Q8)).index = 2 :=
    (goodQ_plus (n := 3) (by norm_num)).relIndex_eq
  have hw : s⁻¹ * g ∈ StatedOmega Q8 :=
    (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨s, hs⟩⁻¹) (b := ⟨g, hg⟩)).2 (by
      simp only [Subgroup.mem_subgroupOf, InvMemClass.coe_inv, inv_mem_iff]
      exact iff_of_false hsΩ hgΩ)
  have hgsw : (⟨g, hg⟩ : isoGrp Q8) =
      ⟨s, hs⟩ * ⟨((⟨s⁻¹ * g, hw⟩ : StatedOmega Q8) : GL (Fin 4 ⊕ Fin 4) (ZMod 2)),
        statedOmega_le_isoGrp _ hw⟩ :=
    Subtype.ext (by simp)
  have hr : c (kappa Q8 ⟨g, hg⟩) =
      plusSwapAut 4 (ZMod 2) (by norm_num) * MulAut.conj (projEquiv ⟨s⁻¹ * g, hw⟩) := by
    rw [hgsw, map_mul, map_mul, congr_kappa_swap, congr_kappa_inner]
  have hFc : F = conjugacyFamily (firstPointStabilizer (n := 4) (K := ZMod 2)) :=
    statedPointFamily_eq_conjugacyFamily (by norm_num)
  have hrF : c (kappa Q8 ⟨g, hg⟩) • F = F := by
    rw [hr, mul_smul, hFc, conj_smul_conjugacyFamily, ← hFc]
    exact plusSwapAut_smul_statedPointFamily 4 (ZMod 2) _
  have hrX : c (kappa Q8 ⟨g, hg⟩) • CX = CXs := by
    rw [hr, mul_smul, conj_smul_conjugacyFamily, plusSwapAut_smul_conjugacyFamily_flag]
  have hrXs : c (kappa Q8 ⟨g, hg⟩) • CXs = CX := by
    rw [hr, mul_smul, conj_smul_conjugacyFamily, plusSwapAut_smul_conjugacyFamily_Xstar]
  apply inducedByIso_of_smul_eq
  have hcomm : c (kappa Q8 ⟨g, hg⟩) * c a = c a * c (kappa Q8 ⟨g, hg⟩) := by
    rw [← map_mul, ← h, map_mul]
  have hfix : c (kappa Q8 ⟨g, hg⟩) • (c a • F) = c a • F := by
    rw [← mul_smul, hcomm, mul_smul, hrF]
  rcases stated_pointFamily_orbit_subset (K := ZMod 2) (n := 4) rfl
      (MulAction.mem_orbit F (c a)) with h1 | h1 | h1
  · exact h1
  · rw [h1, hrX] at hfix
    exact absurd hfix.symm hne
  · rw [h1, hrXs] at hfix
    exact absurd hfix hne

end

end CFSG.LieType.ChevTwo
