module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BRowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyCoverGeneric
public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.Monster.Existence.BabyAmbient
public import CFSG.Monster.Existence.BabyTableIIIOf
public import CFSG.Monster.Existence.TwoPoint.ShapeOneHC
public import CFSG.Monster.B.GSide.Setup
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.IndexTwo
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth21Aut
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Assembly
public import CFSG.Monster.B.TwoA.Amalgam.DerivedCoverMain
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import CFSG.Monster.B.E6.GStarStructure
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
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
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BRow
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import Certificates.Certificate1016
public import Certificates.Certificate1016Base
public import Certificates.Certificate3084
public import Certificates.Certificate3091
public import Certificates.Certificate3167
public import Certificates.Certificate3169
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate3172
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.Monster.GMS CFSG.Monster.Existence CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.GSide
  CFSG.LieType.Chevalley.C2E6Std CFSG.Open

@[expose] def BabyAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), IsSporadic L .B →
    BPair G L K u → ∀ α : MulAut ↥K, ∃ c ∈ L ⊓ centralizer ({u} : Set G),
      ∀ k : K, ((α k : K) : G) = c * (k : G) * c⁻¹

@[expose] def BabySylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), IsSporadic L .B →
    BPair G L K u → ∀ S : Subgroup G, S ≤ L ⊓ centralizer ({u} : Set G) → IsPGroup 2 S →
      (∀ S' : Subgroup G, S' ≤ L ⊓ centralizer ({u} : Set G) → IsPGroup 2 S' → S ≤ S' →
        S' = S) → ∀ z ∈ S, (∀ s ∈ S, z * s = s * z) → z ∈ K

@[expose] def BabyOvergroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), IsSporadic L .B →
    BPair G L K u → ∀ X : Subgroup G, K ≤ X → X ≤ L →
      X ≤ L ⊓ centralizer ({u} : Set G) ∨ X = L

section Mem

theorem babyCover_mem_iff {C : Type*} [Group C] (Ψ : C ≃* ↥Eam) {K : Subgroup C}
    (hK : Nat.card ↥K = 2 * ordTwistedE6 2) : ∀ x, x ∈ K ↔ Ψ x ∈ commutator ↥Eam := by
  intro x
  have hper := short_F4_derived_standard_perfect_cover
  have hEam : Nat.card ↥Eam = 4 * ordTwistedE6 2 := by
    rw [natCard_Eam, card_stdGroup]
    unfold ordTwistedE6
    norm_num
  have hcomm : Nat.card ↥(commutator ↥Eam) = 2 * ordTwistedE6 2 := by
    rw [hper.2.2.2.2.2.2.2.1]
    unfold ordTwistedE6
    norm_num
  have hK1card : Nat.card ↥(K.map Ψ.toMonoidHom) = 2 * ordTwistedE6 2 := by
    rw [Subgroup.card_map_of_injective Ψ.injective]
    exact hK
  have hidx : (K.map Ψ.toMonoidHom).index = 2 := by
    have h := Subgroup.card_mul_index (K.map Ψ.toMonoidHom)
    rw [hK1card, hEam] at h
    have ho : 0 < ordTwistedE6 2 := by unfold ordTwistedE6; norm_num
    nlinarith
  have hle : commutator ↥Eam ≤ K.map Ψ.toMonoidHom := commutator_le_of_index_two hidx
  have hfin : Finite ↥(K.map Ψ.toMonoidHom) :=
    Nat.finite_of_card_ne_zero (by rw [hK1card]; unfold ordTwistedE6; norm_num)
  have hEq : commutator ↥Eam = K.map Ψ.toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hK1card, hcomm])
  rw [hEq, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem babyCover_isIdx2Cover : IsIdx2Cover ↥Eam (commutator ↥Eam) := by
  obtain ⟨hidx, hperf, -, hZ, hc2, hstd, -⟩ := short_F4_derived_standard_perfect_cover
  have hcen : centralizer ((commutator ↥Eam : Subgroup ↥Eam) : Set ↥Eam) = zpowers cE' :=
    CFSG.EvenSmallLie.TwoE6.centralizer_commutator_Eam
  have hZc : center ↥(commutator ↥Eam) = (zpowers cE').subgroupOf (commutator ↥Eam) := by
    rw [← hZ]
    exact (Subgroup.comap_map_eq_self_of_injective (commutator ↥Eam).subtype_injective _).symm
  refine ⟨inferInstance, hidx, ⟨Group.isPerfect_def.1 hperf, ?_⟩, ?_, ?_⟩
  · obtain ⟨e⟩ := hstd
    have := CFSG.Monster.B.E6.stdGroup_isSimpleGroup
    exact ((QuotientGroup.quotientMulEquivOfEq hZc).trans e).isSimpleGroup
  · have h1 : Nat.card ↥(center ↥(commutator ↥Eam)) =
        Nat.card ↥((center ↥(commutator ↥Eam)).map (commutator ↥Eam).subtype) :=
      Nat.card_congr ((center ↥(commutator ↥Eam)).equivMapOfInjective _
        (commutator ↥Eam).subtype_injective).toEquiv
    rw [hZ, hc2] at h1
    exact h1
  · intro x hx
    rw [hcen] at hx
    exact (zpowers_le.2 cE'_mem_commutator) hx

end Mem

section Pair

theorem babyCover_centralizerEquiv_native {u : NativeSporadic.B} (hu2 : orderOf u = 2)
    (hcent : 2 * ordTwistedE6 2 ≤ Nat.card ↥(centralizer ({u} : Set NativeSporadic.B))) :
    Nonempty (↥(centralizer ({u} : Set NativeSporadic.B)) ≃* ↥Eam) := by
  have hT3 := babyTableIII
  obtain ⟨k, hk2, hkc⟩ := hT3.1 u hu2
  have hpos : 0 < babyCentOrder k := by
    fin_cases k <;> simp [babyCentOrder]
  have hk0 : k = 0 := eq_zero_of_le_babyCentOrder (by rw [← hkc]; omega)
  subst hk0
  have hconj1 := isConj_rep_one_of_rank orderOf_phiB_uBar rank_phiB_uBar_sub_one
  have hord1 : orderOf (babyRep 1) = 2 :=
    (orderOf_eq_of_isConj_baby hconj1).symm.trans orderOf_phiB_uBar
  have hrep : BabyInv 0 (babyRep 1) := ⟨hord1, natCard_centralizer_rep_one⟩
  have hconj : IsConj u (babyRep 1) := hT3.2 0 u (babyRep 1) ⟨hk2, hkc⟩ hrep
  have hrank : Matrix.rank (u.val.val - 1) = 1860 := by
    rw [rank_sub_one_of_isConj hconj]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h1860, -⟩ :=
      CFSG.Monster.B.CTIB.native_four_involution_classes
    exact h1860
  obtain ⟨e₁⟩ := nonempty_centralizer_equiv_vStab hu2 hrank
  exact ⟨e₁.trans vStabEam⟩

theorem babyCover_centralizerEquiv {u : Carrier .B} (hu2 : orderOf u = 2)
    (hcent : 2 * ordTwistedE6 2 ≤ Nat.card ↥(centralizer ({u} : Set (Carrier .B)))) :
    Nonempty (↥(centralizer ({u} : Set (Carrier .B))) ≃* ↥Eam) :=
  babyCover_centralizerEquiv_native hu2 hcent

theorem babyCover_pairEquiv {G : Type} [Group G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic ↥L .B) (hP : BPair G L K u) :
    ∃ Ψ : ↥(L ⊓ centralizer ({u} : Set G)) ≃* ↥Eam,
      ∀ x, x ∈ K.subgroupOf (L ⊓ centralizer ({u} : Set G)) ↔ Ψ x ∈ commutator ↥Eam := by
  obtain ⟨hu, hu2, hKL, hKu, hK⟩ := hP
  obtain ⟨eL'⟩ := hL
  let eL := eL'
  have hu2' : orderOf (eL ⟨u, hu⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hu2
  have hKC : K ≤ L ⊓ centralizer ({u} : Set G) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hcard : Nat.card ↥(K.subgroupOf (L ⊓ centralizer ({u} : Set G))) =
      2 * ordTwistedE6 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv]
    exact hK
  have hfin : Finite (Carrier .B) := CFSG.Monster.B.Pinned.finite_B
  let θ := infCentralizerEquiv L eL hu
  have hfinC : Finite ↥(L ⊓ centralizer ({u} : Set G)) := Finite.of_equiv _ θ.symm.toEquiv
  have hle : 2 * ordTwistedE6 2 ≤
      Nat.card ↥(centralizer ({eL ⟨u, hu⟩} : Set (Carrier .B))) := by
    rw [← Nat.card_congr θ.toEquiv, ← hcard]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  obtain ⟨Ψ₀⟩ := babyCover_centralizerEquiv hu2' hle
  exact ⟨θ.trans Ψ₀, babyCover_mem_iff (θ.trans Ψ₀) hcard⟩

theorem babyCover_cover : ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G),
    IsSporadic L .B → BPair G L K u →
      IsIdx2Cover ↥(L ⊓ centralizer ({u} : Set G))
        (K.subgroupOf (L ⊓ centralizer ({u} : Set G))) := by
  intro G _ _ L K u hL hP
  obtain ⟨Ψ, hΨ⟩ := babyCover_pairEquiv hL hP
  have hE : K.subgroupOf (L ⊓ centralizer ({u} : Set G)) =
      (commutator ↥Eam).comap Ψ.toMonoidHom := by
    ext x
    exact hΨ x
  rw [hE]
  exact isIdx2Cover_comap_mulEquiv babyCover_isIdx2Cover Ψ

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup in
theorem babyQuotient_proved : BabyQuotient := by
  intro u K hP
  obtain ⟨Ψ, hΨ⟩ := babyCover_pairEquiv (L := ⊤) (K := K) (u := u) ⟨Subgroup.topEquiv⟩ hP
  have hKC : K ≤ ⊤ ⊓ centralizer ({u} : Set (Carrier .B)) := fun k hk =>
    ⟨mem_top _, mem_centralizer_singleton_iff.2 (hP.2.2.2.1 k hk)⟩
  let θ : ↥K ≃* ↥(commutator ↥Eam) :=
    (Subgroup.subgroupOfEquivOfLe hKC).symm.trans (subgroupEquivOfIff Ψ hΨ)
  obtain ⟨-, -, -, hZ, -, ⟨e⟩, -⟩ := short_F4_derived_standard_perfect_cover
  have hZc : center ↥(commutator ↥Eam) = (zpowers cE').subgroupOf (commutator ↥Eam) := by
    rw [← hZ]
    exact (Subgroup.comap_map_eq_self_of_injective (commutator ↥Eam).subtype_injective _).symm
  exact (CFSG.EvenSmallLie.TwoE6.lieModel_twistedE6_two_iff _).2
    ⟨(quotientCenterEquiv' θ).trans ((QuotientGroup.quotientMulEquivOfEq hZc).trans e)⟩

end Pair

section Aut

theorem babyCover_aut : BabyAut := by
  intro G _ _ L K u hL hP α
  obtain ⟨Ψ, hΨ⟩ := babyCover_pairEquiv hL hP
  have hKC : K ≤ L ⊓ centralizer ({u} : Set G) := fun k hk =>
    ⟨hP.2.2.1 hk, mem_centralizer_singleton_iff.2 (hP.2.2.2.1 k hk)⟩
  let φ := Subgroup.subgroupOfEquivOfLe hKC
  obtain ⟨c, hc⟩ := exists_conj_of_aut_transport Ψ hΨ
    (fun σ => CFSG.EvenSmallLie.TwoE6.exists_eq_conj_of_mulAut σ)
    (φ.trans (α.trans φ.symm))
  refine ⟨(c : G), c.2, fun k => ?_⟩
  have h := congrArg (fun z : ↥(L ⊓ centralizer ({u} : Set G)) => (z : G)) (hc (φ.symm k))
  exact h

theorem babyCoverFacts_of_sylow_overgroups (hsylow : BabySylow)
    (hovergroups : BabyOvergroups) : BabyCoverFacts :=
  ⟨babyCover_cover, babyCover_aut, hsylow, hovergroups⟩

end Aut

end CFSG.EvenSporadicStandard.Induction.Hyp
