module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiIdent
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiLocal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmgMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
public import CFSG.GH74.Uniqueness.Bender.UnitaryDiag
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.JOneRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.TheoremC
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageZero
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwo
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmfLocal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsSylow
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterLevelNuMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterStepMove
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterSwapTNorm
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryFreeOrder
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearFour
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Twist
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Certificate1016Base
public import Certificates.Certificate3085Base
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11
public import Certificates.Kernel.J4Count.KFactsBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.Open
open scoped MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Transport

variable {G : Type} [Group G] {I : Subgroup G} {M : Subgroup I}

theorem gmi_inj : Function.Injective (I.subtype.comp M.subtype) :=
  fun _ _ hab => Subtype.ext (Subtype.ext hab)

theorem gmi_mem_sub₂ {H : Subgroup G} {x : M} :
    x ∈ (H.subgroupOf I).subgroupOf M ↔ ((x : I) : G) ∈ H := by
  rw [mem_subgroupOf, mem_subgroupOf]

theorem gmi_map_sub₂ {H : Subgroup G} (hH : ∀ y ∈ H, ∃ hy : y ∈ I, (⟨y, hy⟩ : I) ∈ M) :
    ((H.subgroupOf I).subgroupOf M).map (I.subtype.comp M.subtype) = H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact gmi_mem_sub₂.mp hx
  · intro hy
    obtain ⟨hyI, hyM⟩ := hH y hy
    exact ⟨⟨⟨y, hyI⟩, hyM⟩, gmi_mem_sub₂.mpr hy, rfl⟩

theorem gmi_card_sub₂ {H : Subgroup G} (hH : ∀ y ∈ H, ∃ hy : y ∈ I, (⟨y, hy⟩ : I) ∈ M) :
    Nat.card ((H.subgroupOf I).subgroupOf M) = Nat.card H := by
  conv_rhs => rw [← gmi_map_sub₂ hH]
  rw [Subgroup.card_map_of_injective gmi_inj]

theorem gmi_iso_sub₂ {H : Subgroup G} (hH : ∀ y ∈ H, ∃ hy : y ∈ I, (⟨y, hy⟩ : I) ∈ M) :
    Nonempty ((H.subgroupOf I).subgroupOf M ≃* H) :=
  ⟨((H.subgroupOf I).subgroupOf M).equivMapOfInjective (I.subtype.comp M.subtype)
    gmi_inj |>.trans (MulEquiv.subgroupCongr (gmi_map_sub₂ hH))⟩

end Transport

theorem gmi_le_commutator_of_simple {Y : Type*} [Group Y] {K : Subgroup Y} [IsSimpleGroup K]
    (hnc : ∃ a b : K, a * b ≠ b * a) : K ≤ ⁅K, K⁆ := by
  have hN : (⁅(⊤ : Subgroup K), ⊤⁆ : Subgroup K) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup K), ⊤⁆ : Subgroup K)
      with hbot | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      exact (mem_centralizer_iff.mp (hle (mem_top b)) a (mem_top a))
    · exact htop
  intro x hx
  have hx' : (⟨x, hx⟩ : K) ∈ (⁅(⊤ : Subgroup K), ⊤⁆ : Subgroup K) := by
    rw [hN]
    exact mem_top _
  have hmap := Subgroup.mem_map_of_mem K.subtype hx'
  rw [Subgroup.map_commutator] at hmap
  exact Subgroup.commutator_mono (map_subtype_le _) (map_subtype_le _) hmap

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmi_card_le_two_mul' {Y : Subgroup G} (hYS : Y ≤ swapS₂ P U T)
    (hYc : ∀ y ∈ Y, ∀ a ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w),
      y * a = a * y) :
    Nat.card Y ≤
      2 * Nat.card (Y ⊓ ((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w)) : Subgroup G) := by
  set A := (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) with hA
  have h1 := relIndex_mul_card (H := U ⊔ T) (K := Y)
  have hle : (U ⊔ T) ⊓ Y ≤ Y ⊓ A := fun x hx => by
    obtain ⟨hxS, hxY⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨hxY, hW.gmf_mem_A_of_comm hxS ?_ ?_⟩
    · exact hYc x hxY _ (mem_sup_right (mem_zpowers _))
    · intro c hc
      exact hYc x hxY c (mem_sup_left hc)
  have h2 : (U ⊔ T).relIndex Y ≤ 2 := by
    rw [← hW.relIndex_SU_S₂]
    exact relIndex_le_of_le_right hYS (by rw [hW.relIndex_SU_S₂]; norm_num)
  have h3 := Subgroup.card_le_of_le hle
  calc Nat.card Y = (U ⊔ T).relIndex Y * Nat.card ((U ⊔ T) ⊓ Y : Subgroup G) := h1.symm
    _ ≤ 2 * Nat.card (Y ⊓ A : Subgroup G) := Nat.mul_le_mul h2 h3

theorem gmi_even : Even f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hW.step.start
  have hS2 := hW.step.card_sylow
  obtain ⟨φ, hφ, -⟩ := h.exists_outHom_of_card_sylow hS2
  obtain ⟨e, Q, hB, -, -⟩ := h.exists_bender_of_card_sylow hS2
  have : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  obtain ⟨Dd, hDn, -, hDcard, -, hQcard⟩ := hB.outer_unitary
  have hout : Nat.card (Outer L) = Nat.gcd 3 (2 ^ f + 1) * (2 * f) := by
    rw [← hDcard, ← hQcard, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup Dd
  have hR2 : IsPGroup 2 φ.range :=
    h.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hdvd : Nat.card φ.range ∣ Nat.card (Outer L) := Subgroup.card_subgroup_dvd_card _
  rw [hout, hk] at hdvd
  have hcop : Nat.Coprime (2 ^ k) (Nat.gcd 3 (2 ^ f + 1)) :=
    (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _)
      (by norm_num : Nat.Coprime 2 3)).pow_left k
  have h2 : 2 ^ k ∣ 2 * f := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨b, hbT, b', hb'T, hbS, hb'S, hbb⟩ := hW.idx
  have hφb : φ ⟨b, hbT⟩ ≠ 1 := fun h1 => hbS ((hφ _).mp h1)
  have hφb' : φ ⟨b', hb'T⟩ ≠ 1 := fun h1 => hb'S ((hφ _).mp h1)
  have hφbb : φ ⟨b, hbT⟩ ≠ φ ⟨b', hb'T⟩ := by
    intro heq
    apply hbb
    have : φ (⟨b, hbT⟩ * (⟨b', hb'T⟩ : T)⁻¹) = 1 := by rw [map_mul, map_inv, heq, mul_inv_cancel]
    exact (hφ _).mp this
  let g : Fin 3 → φ.range := ![1, ⟨φ ⟨b, hbT⟩, ⟨_, rfl⟩⟩, ⟨φ ⟨b', hb'T⟩, ⟨_, rfl⟩⟩]
  have hg : Function.Injective g := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [g] at hij' ⊢ <;>
      first
      | exact (hφb hij'.symm).elim
      | exact (hφb' hij'.symm).elim
      | exact (hφb hij').elim
      | exact (hφb' hij').elim
      | exact (hφbb hij').elim
      | exact (hφbb hij'.symm).elim
  have h3 : 3 ≤ Nat.card φ.range := by
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  rw [hk] at h3
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    interval_cases k <;> norm_num at h3
  have h4 : 2 ^ 2 ∣ 2 * f := (pow_dvd_pow 2 hk2).trans h2
  obtain ⟨c, hc⟩ := h4
  exact ⟨c, by omega⟩

local notation "𝐈" => centralizer ({t * w} : Set G)

theorem gmi_layerHyp
    {J : Subgroup G} (hJ1 : (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ≤ J)
    (hJ2 : J ≤ swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
    (hJ3 : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    {M : Subgroup (centralizer ({t * w} : Set G))}
    (hM : Subgroup.normalClosure ((J.subgroupOf (centralizer ({t * w} : Set G)) :
      Subgroup (centralizer ({t * w} : Set G))) : Set (centralizer ({t * w} : Set G))) = M)
    (hO : CFSG.oddCore M = ⊥) (Q : Sylow 2 (centralizer ({t * w} : Set G)))
    (hQ : (Q : Subgroup (centralizer ({t * w} : Set G))).map
      (centralizer ({t * w} : Set G)).subtype = swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
    (hg1 : CFSG.Open.pCore 2 M ⊔ goldschmidtLayer M = ⊤)
    (hg2 : (J.subgroupOf (centralizer ({t * w} : Set G))).subgroupOf M = CFSG.Open.pCore 2 M ⊔
      Subgroup.closure {x | x ∈ (Q : Subgroup (centralizer ({t * w} : Set G))).subgroupOf M ⊓
        goldschmidtLayer M ∧ x ^ 2 = 1})
    (hg3 : ∀ K : Subgroup M, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K)) :
    ∃ (_ : M.Normal) (QX : Sylow 2 M) (vX eX : M) (τ : MulAut M),
      (∀ y ∈ U₁ ⊓ centralizer ({t * w} : Set G), ∃ hy : y ∈ centralizer ({t * w} : Set G),
        (⟨y, hy⟩ : centralizer ({t * w} : Set G)) ∈ M) ∧
      (∀ y ∈ D ⊓ centralizer ({t * w} : Set G), ∃ hy : y ∈ centralizer ({t * w} : Set G),
        (⟨y, hy⟩ : centralizer ({t * w} : Set G)) ∈ M) ∧
      (((vX : centralizer ({t * w} : Set G)) : G) = t * w) ∧
      (∀ x : M, ((τ x : centralizer ({t * w} : Set G)) : G) =
        t * ((x : centralizer ({t * w} : Set G)) : G) * t⁻¹) ∧
      GmiLayerHyp M f QX ((J.subgroupOf (centralizer ({t * w} : Set G))).subgroupOf M)
        (((U₁ ⊓ centralizer ({t * w} : Set G)).subgroupOf (centralizer ({t * w} : Set G))).subgroupOf M)
        (((szA₁ (szT₁ L T)).subgroupOf (centralizer ({t * w} : Set G))).subgroupOf M)
        (((L ⊓ centralizer ({t * w} : Set G)).subgroupOf (centralizer ({t * w} : Set G))).subgroupOf M)
        (((D ⊓ centralizer ({t * w} : Set G)).subgroupOf (centralizer ({t * w} : Set G))).subgroupOf M)
        vX eX τ := by
  have hMn : M.Normal := by rw [← hM]; exact Subgroup.normalClosure_normal
  have hJM : ∀ y ∈ J, ∃ hy : y ∈ 𝐈, (⟨y, hy⟩ : 𝐈) ∈ M := fun y hy =>
    ⟨(mem_inf.mp (hJ2 hy)).2, by
      rw [← hM]
      exact Subgroup.subset_normalClosure (mem_subgroupOf.mpr hy)⟩
  have hvJ : t * w ∈ J := hJ1 (mem_sup_right (mem_zpowers _))
  have hFJ : U₁ ⊓ 𝐈 ≤ J := le_sup_left.trans hJ1
  have hFM : ∀ y ∈ U₁ ⊓ 𝐈, ∃ hy : y ∈ 𝐈, (⟨y, hy⟩ : 𝐈) ∈ M := fun y hy => hJM y (hFJ hy)
  obtain ⟨hvI, hvM⟩ := hJM _ hvJ
  have htw1 : t * w ≠ 1 := fun h1 => hW.tw_not_mem (by rw [h1]; exact one_mem _)
  have hord : orderOf (t * w) = 2 := orderOf_eq_prime hW.tw_sq htw1
  have hwN : t * w ∈ normalizer (L : Set G) := hW.step.start.le_normalizer hW.tw_mem
  have hout := (hW.step.start.outer_facts_of_card_sylow hW.step.card_sylow hW.tw_mem hW.tw_sq
    hW.tw_not_mem).1
  obtain ⟨⟨eK₀⟩, hK₀simple, hK₀nc, -, -⟩ :=
    u3Star_fixed hW.step.start.two_le hW.step.start.model hord hwN hout
  have hA₁F : szA₁ (szT₁ L T) ≤ U₁ ⊓ 𝐈 := hW.gmf_szA₁_le_F
  have hA₁K₀ : szA₁ (szT₁ L T) ≤ L ⊓ 𝐈 := fun a ha =>
    mem_inf.mpr ⟨szT₁_le_right L T (szA₁_le _ ha), (mem_inf.mp (hA₁F ha)).2⟩
  have hcardA₁ : Nat.card (szA₁ (szT₁ L T)) = 2 ^ f :=
    (hW.step.start.facts_of_card_sylow hW.step.card_sylow).2.1
  set M' := M.map 𝐈.subtype with hM'
  have hM'n : ∀ g ∈ 𝐈, ∀ y ∈ M', g * y * g⁻¹ ∈ M' := by
    rintro g hg _ ⟨m, hm, rfl⟩
    exact ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, hMn.conj_mem m hm _, rfl⟩
  have hK₀M' : L ⊓ 𝐈 ≤ M' := by
    have hN := (Subgroup.isSimpleGroup_iff.mp hK₀simple).2 (M' ⊓ (L ⊓ 𝐈)) inf_le_right
      ⟨fun x hx g => mem_subgroupOf.mpr (mem_inf.mpr
        ⟨hM'n _ (mem_inf.mp g.2).2 _ (mem_inf.mp (mem_subgroupOf.mp hx)).1,
          mul_mem (mul_mem g.2 (mem_inf.mp (mem_subgroupOf.mp hx)).2) (inv_mem g.2)⟩)⟩
    rcases hN with hbot | heq
    · exfalso
      have hA₁le : szA₁ (szT₁ L T) ≤ M' ⊓ (L ⊓ 𝐈) := fun a ha => by
        obtain ⟨haI, haM⟩ := hJM a (hFJ (hA₁F ha))
        exact mem_inf.mpr ⟨⟨⟨a, haI⟩, haM, rfl⟩, hA₁K₀ ha⟩
      rw [hbot, le_bot_iff] at hA₁le
      rw [hA₁le, Subgroup.card_bot] at hcardA₁
      have : 2 ≤ 2 ^ f := Nat.le_self_pow (by have := hW.step.start.two_le; omega) 2
      omega
    · rw [← heq]
      exact inf_le_left
  have hK₀M : ∀ y ∈ L ⊓ 𝐈, ∃ hy : y ∈ 𝐈, (⟨y, hy⟩ : 𝐈) ∈ M := fun y hy => by
    obtain ⟨m, hm, rfl⟩ := hK₀M' hy
    exact ⟨m.2, hm⟩
  have hDK₀ : D ⊓ 𝐈 ≤ L ⊓ 𝐈 := inf_le_inf_right _ hW.step.cartan.le
  have hDM : ∀ y ∈ D ⊓ 𝐈, ∃ hy : y ∈ 𝐈, (⟨y, hy⟩ : 𝐈) ∈ M := fun y hy => hK₀M y (hDK₀ hy)
  have hA₁M : ∀ y ∈ szA₁ (szT₁ L T), ∃ hy : y ∈ 𝐈, (⟨y, hy⟩ : 𝐈) ∈ M := fun y hy =>
    hK₀M y (hA₁K₀ hy)
  obtain ⟨e, heL, hev, -, heU, -, -, -, hefix⟩ := hW.gmi_exists_torus
  have heK₀ : e ∈ L ⊓ 𝐈 := mem_inf.mpr ⟨heL, mem_centralizer_singleton_iff.mpr hev⟩
  obtain ⟨heI, heM⟩ := hK₀M e heK₀
  have hQS : IsSylowOf 2 ((Q : Subgroup 𝐈) ⊓ M) M :=
    (gmi_isSylowOf_top Q).inf_of_le_normalizer le_top (gmi_top_le_normalizer hMn)
  obtain ⟨QX, hQX⟩ := hQS
  have hQXmem : ∀ x : M, x ∈ (QX : Subgroup M) ↔ (x : 𝐈) ∈ (Q : Subgroup 𝐈) := by
    intro x
    constructor
    · intro hx
      have := Subgroup.mem_map_of_mem M.subtype hx
      rw [hQX] at this
      exact (mem_inf.mp this).1
    · intro hx
      have hmem : (x : 𝐈) ∈ (QX : Subgroup M).map M.subtype := by
        rw [hQX]
        exact mem_inf.mpr ⟨hx, x.2⟩
      obtain ⟨y, hy, hyx⟩ := hmem
      rwa [show y = x from Subtype.ext hyx] at hy
  have hQXeq : (QX : Subgroup M) = (Q : Subgroup 𝐈).subgroupOf M := by
    ext x
    rw [hQXmem, mem_subgroupOf]
  have hQmem : ∀ x : 𝐈, x ∈ (Q : Subgroup 𝐈) ↔ (x : G) ∈ swapS₂ P U T ⊓ 𝐈 := by
    intro x
    rw [← hQ]
    constructor
    · exact fun hx => mem_map_of_mem _ hx
    · rintro ⟨y, hy, hyx⟩
      rwa [show y = x from Subtype.ext hyx] at hy
  have htI : t ∈ 𝐈 := hW.gmg_t_mem_I
  set τ : MulAut M := MulAut.conjNormal (⟨t, htI⟩ : 𝐈) with hτdef
  have hτ : ∀ x : M, ((τ x : 𝐈) : G) = t * ((x : 𝐈) : G) * t⁻¹ := fun x => by
    rw [hτdef, MulAut.conjNormal_apply]
    rfl
  have htt : t * t = 1 := by rw [← sq]; exact hW.step.start.sq_eq_one
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htS₀ : (⟨t, htI⟩ : 𝐈) ∈ (Q : Subgroup 𝐈) :=
    (hQmem _).mpr (mem_inf.mpr ⟨hW.le_S₂ (mem_sup_right hW.t_mem), htI⟩)
  have htwF : t * w ∉ U₁ ⊓ 𝐈 := fun h' => hW.tw_not_mem (mem_sup_left
    (hW.level.muOne_mem_T₁_of_mem_T hW.step (mem_inf.mp h').1 hW.tw_mem))
  refine ⟨hMn, QX, ⟨⟨t * w, hvI⟩, hvM⟩, ⟨⟨e, heI⟩, heM⟩, τ, hFM, hDM, rfl, hτ, ?_⟩
  obtain ⟨eX₀⟩ := gmi_iso_sub₂ hK₀M
  have hsimpX : IsSimpleGroup
      (((L ⊓ 𝐈).subgroupOf 𝐈).subgroupOf M) := by
    have := hK₀simple
    exact eX₀.isSimpleGroup
  have hncX : ∃ a b : (((L ⊓ 𝐈).subgroupOf 𝐈).subgroupOf M), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK₀nc
    refine ⟨eX₀.symm a, eX₀.symm b, fun h' => hab ?_⟩
    have := congrArg eX₀ h'
    simpa using this
  set φ : M →* G := (𝐈).subtype.comp M.subtype with hφ
  exact {
    odd := hO
    gen := hg1
    J_eq := by rw [hg2, gmiOmega, hQXeq]
    type := hg3
    J_comm := fun a ha b hb =>
      Subtype.ext (Subtype.ext (hJ3 _ (gmi_mem_sub₂.mp ha) _ (gmi_mem_sub₂.mp hb)))
    F_le := fun x hx => gmi_mem_sub₂.mpr (hFJ (gmi_mem_sub₂.mp hx))
    F_sq := fun x hx => Subtype.ext (Subtype.ext (by
      have := hW.F_sq (gmi_mem_sub₂.mp hx)
      simpa using this))
    card_F := by rw [gmi_card_sub₂ hFM, hW.card_F]
    two_le := hW.step.start.two_le
    even := hW.gmi_even
    v_mem := gmi_mem_sub₂.mpr hvJ
    v_comm := fun y => Subtype.ext (Subtype.ext
      (mem_centralizer_singleton_iff.mp (y : 𝐈).2).symm)
    v_not_mem := fun hv => htwF (gmi_mem_sub₂.mp hv)
    v_sq := Subtype.ext (Subtype.ext (by simpa using hW.tw_sq))
    L4 := by
      intro Y hYQ hYc
      have hφv : φ ⟨⟨t * w, hvI⟩, hvM⟩ = t * w := rfl
      have hAmap : ((((U₁ ⊓ 𝐈).subgroupOf 𝐈).subgroupOf M) ⊔
          zpowers (⟨⟨t * w, hvI⟩, hvM⟩ : M)).map φ = (U₁ ⊓ 𝐈) ⊔ zpowers (t * w) := by
        rw [Subgroup.map_sup, gmi_map_sub₂ hFM, MonoidHom.map_zpowers, hφv]
      have hYS : Y.map φ ≤ swapS₂ P U T := by
        rintro _ ⟨y, hy, rfl⟩
        exact (mem_inf.mp ((hQmem _).mp ((hQXmem y).mp (hYQ hy)))).1
      have hYc' : ∀ y ∈ Y.map φ, ∀ a ∈ (U₁ ⊓ 𝐈) ⊔ zpowers (t * w), y * a = a * y := by
        rintro _ ⟨y, hy, rfl⟩ a ha
        rw [← hAmap] at ha
        obtain ⟨a', ha', rfl⟩ := ha
        rw [← map_mul, ← map_mul, hYc y hy a' ha']
      have h1 := hW.gmi_card_le_two_mul' hYS hYc'
      rwa [Subgroup.card_map_of_injective gmi_inj, ← hAmap,
        ← Subgroup.map_inf _ _ _ gmi_inj, Subgroup.card_map_of_injective gmi_inj] at h1
    L6 := by
      have h1 : Nat.card (QX : Subgroup M) = Nat.card ((Q : Subgroup 𝐈) ⊓ M : Subgroup 𝐈) := by
        rw [← hQX, Subgroup.card_map_of_injective M.subtype_injective]
      have h2 : Nat.card (Q : Subgroup 𝐈) = Nat.card (swapS₂ P U T ⊓ 𝐈 : Subgroup G) := by
        rw [← hQ, Subgroup.card_map_of_injective (𝐈).subtype_injective]
      have h3 := Subgroup.card_le_of_le (inf_le_left : (Q : Subgroup 𝐈) ⊓ M ≤ Q)
      rw [h1]
      exact h3.trans (h2 ▸ hW.gmi_card_S₀_le)
    K₀_iso := ⟨eX₀.trans eK₀⟩
    K₀_simple := fun N hN hNn => (Subgroup.isSimpleGroup_iff.mp hsimpX).2 N hN
      ⟨fun x hx g => mem_subgroupOf.mpr (hNn g g.2 x (mem_subgroupOf.mp hx))⟩
    K₀_perfect := gmi_le_commutator_of_simple hncX
    card_K₀ := by
      rw [gmi_card_sub₂ hK₀M, Nat.card_congr eK₀.toEquiv,
        CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_even
          (by have := hW.step.start.two_le; omega)]
    A₁_le_K₀ := fun x hx => gmi_mem_sub₂.mpr (hA₁K₀ (gmi_mem_sub₂.mp hx))
    A₁_le_F := fun x hx => gmi_mem_sub₂.mpr (hA₁F (gmi_mem_sub₂.mp hx))
    card_A₁ := by rw [gmi_card_sub₂ hA₁M, hcardA₁]
    e_mem := gmi_mem_sub₂.mpr heK₀
    e_F := fun x hx => gmi_mem_sub₂.mpr (by
      have hxF := gmi_mem_sub₂.mp hx
      exact mem_inf.mpr ⟨(mem_normalizer_iff.mp heU _).mp (mem_inf.mp hxF).1,
        mul_mem (mul_mem heI (mem_inf.mp hxF).2) (inv_mem heI)⟩)
    e_fix := fun x hx hex => Subtype.ext (Subtype.ext
      (hefix _ (gmi_mem_sub₂.mp hx) (congrArg (fun z : M => ((z : 𝐈) : G)) hex)))
    τ_inv := fun x => Subtype.ext (Subtype.ext (by
      rw [hτ, hτ, htinv]
      calc t * (t * ((x : 𝐈) : G) * t) * t = (t * t) * ((x : 𝐈) : G) * (t * t) := by group
        _ = ((x : 𝐈) : G) := by rw [htt, one_mul, mul_one]))
    τ_K₀ := fun x hx => Subtype.ext (Subtype.ext (by
      rw [hτ]
      have hxL := (mem_inf.mp (gmi_mem_sub₂.mp hx)).1
      rw [← mem_centralizer_iff.mp hW.step.start.mem _ hxL, mul_inv_cancel_right]))
    τ_F := fun x hx => gmi_mem_sub₂.mpr (by rw [hτ]; exact hW.gmg_t_conj_F (gmi_mem_sub₂.mp hx))
    τ_Q := fun x hx => by
      rw [hQXmem] at hx ⊢
      rw [show (τ x : 𝐈) = ⟨t, htI⟩ * (x : 𝐈) * (⟨t, htI⟩ : 𝐈)⁻¹ from Subtype.ext (hτ x)]
      exact mul_mem (mul_mem htS₀ hx) (inv_mem htS₀)
    τ_move := by
      obtain ⟨c, hc, hct⟩ := hW.gmg_exists_not_commute t (Or.inl rfl)
      obtain ⟨hcI, hcM⟩ := hFM c hc
      refine ⟨⟨⟨c, hcI⟩, hcM⟩, gmi_mem_sub₂.mpr hc, fun h' => hct ?_⟩
      have := congrArg (fun z : M => ((z : 𝐈) : G)) h'
      simp only [hτ] at this
      calc c * t = t * c * t⁻¹ * t := by rw [this]
        _ = t * c := by group
    D_le := fun x hx => gmi_mem_sub₂.mpr (hDK₀ (gmi_mem_sub₂.mp hx))
    D_odd := by rw [gmi_card_sub₂ hDM]; exact hW.gmg_odd_card_D_inf
    D_τ := fun x hx => Subtype.ext (Subtype.ext (by
      rw [hτ]
      have hxL := hW.step.cartan.le (mem_inf.mp (gmi_mem_sub₂.mp hx)).1
      rw [← mem_centralizer_iff.mp hW.step.start.mem _ hxL, mul_inv_cancel_right]))
    D_F := fun d hd x hx => gmi_mem_sub₂.mpr
      ((mem_normalizer_iff.mp (hW.gmg_D_le_normalizer_F (gmi_mem_sub₂.mp hd)) _).mp
        (gmi_mem_sub₂.mp hx)) }

end U3C1OuterSwapHigh

theorem u3C1GmgIdentGoldInput_holds
    (hC4 : GmiCatFourInput) (hCS : GmiCatSimpleInput) (hSchur : GmiCatSchurInput) :
    U3C1GmgIdentGoldInput := by
  intro G _ _ L f t T R₂ D d V U U₁ w s P hW _ _ _ _ _ J hJ1 hJ2 hJ3 _ M hM hO Q hQ hg1 hg2 hg3
  obtain ⟨hMn, QX, vX, eX, τ, hFM, hDM, -, hτ, hX⟩ :=
    hW.gmi_layerHyp hJ1 hJ2 hJ3 hM hO Q hQ hg1 hg2 hg3
  have hφτ : ∀ x : M, ((centralizer ({t * w} : Set G)).subtype.comp M.subtype) (τ x) =
      t * ((centralizer ({t * w} : Set G)).subtype.comp M.subtype) x * t⁻¹ := fun x => hτ x
  set φ : M →* G := (centralizer ({t * w} : Set G)).subtype.comp M.subtype with hφ
  have hφI : ∀ x : M, φ x ∈ centralizer ({t * w} : Set G) := fun x =>
    (x : centralizer ({t * w} : Set G)).2
  have hFmap := gmi_map_sub₂ hFM
  have hsyl : ∀ {A B : Subgroup M}, IsSylowOf 2 A B → IsSylowOf 2 (A.map φ) (B.map φ) := by
    intro A B hAB
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 := (isSylowOf_map_subtype_iff M).mpr hAB
    have h2 := (isSylowOf_map_subtype_iff (centralizer ({t * w} : Set G))).mpr h1
    rwa [Subgroup.map_map, Subgroup.map_map] at h2
  rcases hX.ident hC4 hCS hSchur with ⟨K, p, n, hp, hpn, ⟨eK⟩, hFK, hDK⟩ |
      ⟨K₁, E₁, p, n, hp, hpn, ⟨eK⟩, hcomm, hFK, hdec, hE₁K, hE₁N, hE₁odd, hDE⟩
  · left
    refine ⟨K.map φ, p, n, hp, hpn, ⟨(K.equivMapOfInjective φ gmi_inj).symm.trans eK⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact hφI x
    · have := hsyl hFK
      rwa [hFmap] at this
    · intro y hy
      obtain ⟨hyI, hyM⟩ := hDM y hy
      exact ⟨⟨⟨y, hyI⟩, hyM⟩, hDK (gmi_mem_sub₂.mpr hy), rfl⟩
  · right
    have hFK₁ : (U₁ ⊓ centralizer ({t * w} : Set G)) ⊓ K₁.map φ =
        ((((U₁ ⊓ centralizer ({t * w} : Set G)).subgroupOf
          (centralizer ({t * w} : Set G))).subgroupOf M) ⊓ K₁).map φ := by
      rw [Subgroup.map_inf _ _ _ gmi_inj, hFmap]
    have hmemFK : ∀ {x : M}, x ∈ (((U₁ ⊓ centralizer ({t * w} : Set G)).subgroupOf
        (centralizer ({t * w} : Set G))).subgroupOf M) ⊓ K₁ →
        φ x ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊓ K₁.map φ := fun hx => by
      rw [hFK₁]
      exact Subgroup.mem_map_of_mem φ hx
    refine ⟨K₁.map φ, E₁.map φ, p, n, hp, hpn,
      ⟨(K₁.equivMapOfInjective φ gmi_inj).symm.trans eK⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact hφI x
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← hφτ b, ← map_mul, ← map_mul, hcomm a ha b hb]
    · rw [hFK₁]
      exact hsyl hFK
    · intro x hx
      obtain ⟨hxI, hxM⟩ := hFM x hx
      obtain ⟨x₁, hx₁, x₂, hx₂, hx₁₂⟩ := hdec ⟨⟨x, hxI⟩, hxM⟩ (gmi_mem_sub₂.mpr hx)
      refine ⟨φ x₁, hmemFK hx₁, φ x₂, hmemFK hx₂, ?_⟩
      rw [← hφτ x₂, ← map_mul, ← hx₁₂]
      rfl
    · exact Subgroup.map_mono hE₁K
    · rintro _ ⟨g, hg, rfl⟩
      have hgN := hE₁N hg
      have hconj : ∀ g' : M, g' ∈ normalizer (((((U₁ ⊓ centralizer ({t * w} : Set G)).subgroupOf
          (centralizer ({t * w} : Set G))).subgroupOf M) ⊓ K₁ : Subgroup M) : Set M) →
          ∀ y ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊓ K₁.map φ,
            φ g' * y * (φ g')⁻¹ ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊓ K₁.map φ := by
        intro g' hg' y hy
        rw [hFK₁] at hy ⊢
        obtain ⟨y', hy', rfl⟩ := hy
        rw [← map_inv, ← map_mul, ← map_mul]
        exact Subgroup.mem_map_of_mem φ ((mem_normalizer_iff.mp hg' y').mp hy')
      refine gmg_mem_normalizer (hconj g hgN) (fun y hy => ?_)
      have := hconj g⁻¹ (inv_mem hgN) y hy
      rwa [map_inv, inv_inv] at this
    · rw [Subgroup.card_map_of_injective gmi_inj]
      exact hE₁odd
    · intro y hy
      obtain ⟨hyI, hyM⟩ := hDM y hy
      obtain ⟨e₁, he₁, e₂, he₂, he⟩ := hDE ⟨⟨y, hyI⟩, hyM⟩ (gmi_mem_sub₂.mpr hy)
      refine ⟨φ e₁, Subgroup.mem_map_of_mem φ he₁, φ e₂, Subgroup.mem_map_of_mem φ he₂, ?_⟩
      rw [← hφτ e₂, ← map_mul, ← he]
      rfl

end CFSG.SeitzReduction.RankOne
