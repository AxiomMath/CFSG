module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Five
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Nine
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.Statements
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.JRFacts

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

theorem mem_normalizer_of_forall_mem_iff_R4 [Finite G] {H K A B : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G))
    (hA : g ∈ normalizer (A : Set G))
    (hB : ∀ x, x ∈ B ↔ x ∈ H ∧ ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ A) :
    g ∈ normalizer (B : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxH, hxc⟩ := (hB x).1 hx
  refine (hB _).2 ⟨(mem_normalizer_iff.1 hH x).1 hxH, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ K := by
    have := (mem_normalizer_iff.1 (inv_mem hK) y).1 hy
    rwa [inv_inv] at this
  have h1 := (mem_normalizer_iff.1 hA _).1 (hxc _ hy')
  rwa [show g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ =
    g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ * y⁻¹ by group] at h1

theorem mem_map_upperCentralSeries_succ_iff_R4 {H T : Subgroup G} {n : ℕ}
    (hT : (Subgroup.upperCentralSeries H n).map H.subtype = T) {x : G} :
    x ∈ (Subgroup.upperCentralSeries H (n + 1)).map H.subtype ↔
      x ∈ H ∧ ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ T := by
  rw [mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun y hy => ?_⟩
    rw [← hT]
    exact ⟨z * ⟨y, hy⟩ * z⁻¹ * ⟨y, hy⟩⁻¹, Subgroup.mem_upperCentralSeries_succ_iff.1 hz _, rfl⟩
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_upperCentralSeries_succ_iff.2 fun y => ?_, rfl⟩
    have hy := h y y.2
    rw [← hT] at hy
    obtain ⟨w, hw, hw'⟩ := hy
    have hw'' : w = ⁅(⟨x, hx⟩ : H), y⁆ := Subtype.ext hw'
    rwa [← hw'']

theorem mem_of_mul_comm_R4 {A : Subgroup G} {a b : G} (h : a * b = b * a) :
    a * b * a⁻¹ * b⁻¹ ∈ A := by
  rw [show a * b * a⁻¹ * b⁻¹ = 1 from commutatorElement_eq_one_iff_mul_comm.2 h]
  exact one_mem _

theorem comm_swap_mem_R4 {A : Subgroup G} {a b : G} (h : a * b * a⁻¹ * b⁻¹ ∈ A) :
    b * a * b⁻¹ * a⁻¹ ∈ A := by
  have := inv_mem h
  rwa [show (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ by group] at this

theorem mul_comm_of_comm_mem_bot_R4 {a b : G} (h : a * b * a⁻¹ * b⁻¹ ∈ (⊥ : Subgroup G)) :
    a * b = b * a :=
  (commutatorElement_eq_one_iff_mul_comm (g₁ := a) (g₂ := b)).1 (mem_bot.1 h)

end Generic

set_option hygiene false in
local macro "layer_ctx" : tactic => `(tactic| (
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h59e := h.yamadaY₂_eq d hlay
  have h520 := h.yamada_5_20 d hlay
  have h521 := h.yamada_5_21 d hlay
  have h5221 := h.yamada_5_22_1 d hlay
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have h515 := h.yamada_5_15 d hNH h561 h562 h591 h592 h593
  have h524 := h.yamada_5_24 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
  have h525 := h.yamada_5_25 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Basic

theorem yamadaR₃_le_sup_yamadaW₃_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaR₃ d t ≤ yamadaR₂ d t ⊔ yamadaW₃ d t := by
  layer_ctx
  have hR₃ := (h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102).2
  rw [hR₃, h.yamadaL₃_eq_sup d hlay, ← h.yamadaM₂_sup_yamadaW₃ d hlay]
  have hL₂R₂ : yamadaL₂ d t ≤ yamadaR₂ d t := le_sup_left
  have hM₂R₂ : yamadaM₂ d t ≤ yamadaR₂ d t :=
    (le_sup_left.trans (le_of_eq h591.1.symm)).trans hL₂R₂
  have htR₂ : zpowers t ≤ yamadaR₂ d t := (zpowers_le).2 (hL₂R₂ (h.t_mem_yamadaL₂ d))
  exact sup_le (sup_le (sup_le (hM₂R₂.trans le_sup_left) le_sup_right)
    (htR₂.trans le_sup_left)) ((le_sup_right : d.S.map L.subtype ≤ yamadaR₂ d t).trans le_sup_left)

theorem yamadaR₂_le_yamadaR₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₂ d t ≤ yamadaR₄ d t := by
  layer_ctx
  exact h514.2.2.2.1.1.trans h514.2.2.2.2.1.1

theorem yamadaW₃_le_yamadaR₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaW₃ d t ≤ yamadaR₄ d t := by
  layer_ctx
  exact ((inf_le_left : yamadaW₃ d t ≤ yamadaL₃ d t).trans
    (h.yamadaL₃_le_yamadaR₃_D3 d hlay)).trans h514.2.2.2.2.1.1

theorem S_map_le_yamadaR₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.S.map L.subtype ≤ yamadaR₄ d t :=
  (le_sup_right : d.S.map L.subtype ≤ yamadaR₂ d t).trans (h.yamadaR₂_le_yamadaR₄_R4 d hlay)

theorem yamadaD₁_le_yamadaR₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaD₁ d t ≤ yamadaR₄ d t := by
  layer_ctx
  exact (((h.yamadaD₁_le_yamadaD₃_C9 d hNH h561 h562 h591 h592 h593).trans
    (inf_le_left : yamadaD₃ d t ≤ yamadaS₃ d t)).trans
      (inf_le_left : yamadaS₃ d t ≤ yamadaR₃ d t)).trans h514.2.2.2.2.1.1

theorem yamadaS₁_le_yamadaR₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaS₁ d t ≤ yamadaR₄ d t :=
  sup_le (h.S_map_le_yamadaR₄_R4 d hlay) (h.yamadaD₁_le_yamadaR₄_R4 d hlay)

theorem yamadaR₄_le_sup_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaR₄ d t ≤ yamadaR₂ d t ⊔ yamadaW₃ d t ⊔ yamadaM₄ d t := by
  layer_ctx
  have htR₂ : zpowers t ≤ yamadaR₂ d t :=
    (zpowers_le).2 ((le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t) (h.t_mem_yamadaL₂ d))
  have hR₃ := h.yamadaR₃_le_sup_yamadaW₃_R4 d hlay
  rw [h524.2.1.1, h524.1.1]
  exact sup_le (sup_le le_sup_right (htR₂.trans (le_sup_left.trans le_sup_left)))
    (hR₃.trans le_sup_left)

theorem yamadaR₄_le_of_le_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {K : Subgroup G} (h₂ : yamadaR₂ d t ≤ K) (h₃ : yamadaW₃ d t ≤ K)
    (h₄ : yamadaM₄ d t ≤ K) : yamadaR₄ d t ≤ K :=
  (h.yamadaR₄_le_sup_R4 d hlay).trans (sup_le (sup_le h₂ h₃) h₄)

end Basic

section Normalizers

theorem yamadaR₄_le_normalizer_yamadaY₁_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t ≤ normalizer (yamadaY₁ d t : Set G) := by
  layer_ctx
  exact h514.2.2.2.2.2.1.trans
    (h.yamadaR₅_le_normalizer_yamadaY₁ d hNH h561 h562 h591 h592 h593)

theorem yamadaR₄_le_normalizer_yamadaY₂_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t ≤ normalizer (yamadaY₂ d t : Set G) := by
  layer_ctx
  exact h.yamadaR₄_le_normalizer_yamadaY₂ d hNH h561 h562 h591 h592 h593 h5221

theorem yamadaR₄_le_normalizer_yamadaM₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t ≤ normalizer (yamadaM₄ d t : Set G) := fun _ hg =>
  Common.mem_normalizer_inf (le_normalizer hg)
    (mem_normalizer_centralizer_C8 (h.yamadaR₄_le_normalizer_yamadaY₂_R4 d hlay hg))

theorem yamadaW₂_le_yamadaR₃_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaW₂ d t ≤ yamadaR₃ d t :=
  (sup_le_sup_right (map_mono d.W_le_F) _).trans (h.yamadaF₂_le_yamadaR₃ d hlay)

theorem yamadaR₄_le_normalizer_yamadaW₂_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t ≤ normalizer (yamadaW₂ d t : Set G) := by
  layer_ctx
  haveI hchar : ((yamadaW₂ d t).subgroupOf (yamadaR₃ d t)).Characteristic :=
    characteristic_iff_map_le.2 fun ϕ => by
      rintro _ ⟨x, hx, rfl⟩
      replace hx := mem_subgroupOf.1 hx
      rw [mem_subgroupOf]
      exact h.automorphism_mem_yamadaW₂ d hlay ϕ hx
  intro g hg
  have := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((yamadaW₂ d t).subgroupOf (yamadaR₃ d t)) (h514.2.2.2.2.1.2 hg)
  rwa [map_subgroupOf_eq_of_le (h.yamadaW₂_le_yamadaR₃_R4 d hlay)] at this

theorem yamadaR₄_le_normalizer_yamadaF₃_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t ≤ normalizer (yamadaF₃ d t : Set G) := by
  layer_ctx
  intro g hg
  have := normalizer_le_normalizer_commutator_C8 (yamadaR₄ d t) (le_normalizer hg)
  rwa [h524.2.2] at this

theorem yamadaW₃_eq_inf_centralizer_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaW₃ d t = yamadaF₃ d t ⊓ centralizer (yamadaW₂ d t : Set G) := by
  refine le_antisymm (le_inf (h.yamadaW₃_le_yamadaF₃ d hlay) inf_le_right) (fun x hx => ?_)
  obtain ⟨hxF₃, hxC⟩ := mem_inf.1 hx
  exact mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hxF₃).1).1, hxC⟩

theorem yamadaR₄_le_normalizer_yamadaW₃_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t ≤ normalizer (yamadaW₃ d t : Set G) := by
  intro g hg
  rw [h.yamadaW₃_eq_inf_centralizer_R4 d hlay]
  exact Common.mem_normalizer_inf (h.yamadaR₄_le_normalizer_yamadaF₃_R4 d hlay hg)
    (mem_normalizer_centralizer_C8 (h.yamadaR₄_le_normalizer_yamadaW₂_R4 d hlay hg))

end Normalizers

section Series

theorem series_yamadaR₂_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (∀ x, x ∈ d.V.map L.subtype ↔ x ∈ yamadaR₂ d t ∧
      ∀ y ∈ yamadaR₂ d t, x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G)) ∧
    (∀ x, x ∈ yamadaY₁ d t ↔ x ∈ yamadaR₂ d t ∧
      ∀ y ∈ yamadaR₂ d t, x * y * x⁻¹ * y⁻¹ ∈ d.V.map L.subtype) ∧
    (∀ x, x ∈ yamadaW₂ d t ⊔ zpowers t ↔ x ∈ yamadaR₂ d t ∧
      ∀ y ∈ yamadaR₂ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaY₁ d t) := by
  layer_ctx
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [← h5101.1]
    exact mem_map_upperCentralSeries_succ_iff_R4 (n := 0) (map_upperCentralSeries_zero _)
  · rw [← h5101.2.1]
    exact mem_map_upperCentralSeries_succ_iff_R4 (n := 1) h5101.1
  · rw [← h5101.2.2.1]
    exact mem_map_upperCentralSeries_succ_iff_R4 (n := 2) h5101.2.1

theorem mem_yamadaR₂_of_commutator_mem_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {A : Subgroup G} (hA : A ≤ yamadaS₁ d t) {x : G}
    (hx : x ∈ yamadaR₄ d t) (hc : ∀ y ∈ yamadaR₄ d t, x * y * x⁻¹ * y⁻¹ ∈ A) :
    x ∈ yamadaR₂ d t := by
  layer_ctx
  have hS₁ := h.yamadaS₁_le_yamadaR₄_R4 d hlay
  have hx' : x ∈ yamadaR₅ d t ⊓ normalizer (yamadaS₁ d t : Set G) := by
    refine mem_inf.2 ⟨(mem_inf.1 hx).1, mem_normalizer_fintype fun s hs => ?_⟩
    have := mul_mem (hA (hc s (hS₁ hs))) hs
    rwa [show x * s * x⁻¹ * s⁻¹ * s = x * s * x⁻¹ by group] at this
  rwa [h515.1] at hx'

theorem mem_yamadaV_iff_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} :
    x ∈ d.V.map L.subtype ↔
      x ∈ yamadaR₄ d t ∧ ∀ y ∈ yamadaR₄ d t, x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) := by
  layer_ctx
  obtain ⟨E1, -, -⟩ := h.series_yamadaR₂_R4 d hlay
  have hR₂R₄ := h.yamadaR₂_le_yamadaR₄_R4 d hlay
  constructor
  · intro hx
    obtain ⟨hxR₂, hxc⟩ := (E1 x).1 hx
    have hxY₂ : x ∈ yamadaY₂ d t := yamadaV₁_le_yamadaY₂ d (V_le_yamadaV₁ d h562 hx)
    have hxW₂ : x ∈ yamadaW₂ d t := (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hxY₂
    have hle : yamadaR₄ d t ≤ centralizer ({x} : Set G) := by
      refine h.yamadaR₄_le_of_le_R4 d hlay (fun y hy => ?_) (fun w hw => ?_) (fun m hm => ?_)
      · exact mem_centralizer_singleton_iff.2 (mul_comm_of_comm_mem_bot_R4 (hxc y hy)).symm
      · exact mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (mem_inf.1 hw).2 x hxW₂).symm
      · exact mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (mem_inf.1 hm).2 x hxY₂).symm
    exact ⟨hR₂R₄ hxR₂, fun y hy =>
      mem_of_mul_comm_R4 (mem_centralizer_singleton_iff.1 (hle hy)).symm⟩
  · rintro ⟨hx, hc⟩
    exact (E1 x).2 ⟨h.mem_yamadaR₂_of_commutator_mem_R4 d hlay bot_le hx hc,
      fun y hy => hc y (hR₂R₄ hy)⟩

theorem yamadaR₄_le_normalizer_V_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaR₄ d t ≤ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) := fun g hg =>
  mem_normalizer_fintype fun b hb => by
    have hbg : b * g = g * b :=
      mul_comm_of_comm_mem_bot_R4 (((h.mem_yamadaV_iff_R4 d hlay).1 hb).2 g hg)
    rw [← hbg, mul_inv_cancel_right]
    exact hb

theorem mem_yamadaY₁_iff_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} :
    x ∈ yamadaY₁ d t ↔ x ∈ yamadaR₄ d t ∧
      ∀ y ∈ yamadaR₄ d t, x * y * x⁻¹ * y⁻¹ ∈ d.V.map L.subtype := by
  layer_ctx
  obtain ⟨-, E2, -⟩ := h.series_yamadaR₂_R4 d hlay
  have hR₂R₄ := h.yamadaR₂_le_yamadaR₄_R4 d hlay
  have hY₁Y₂ := h.yamadaY₁_le_yamadaY₂ d hlay
  constructor
  · intro hx
    obtain ⟨hxR₂, -⟩ := (E2 x).1 hx
    have hK : ∀ g ∈ yamadaR₄ d t, ∀ y ∈ yamadaY₁ d t, g * y * g⁻¹ ∈ yamadaY₁ d t :=
      fun g hg y hy =>
        (mem_normalizer_iff.1 (h.yamadaR₄_le_normalizer_yamadaY₁_R4 d hlay hg) y).1 hy
    have hB : ∀ g ∈ yamadaR₄ d t, ∀ b ∈ d.V.map L.subtype, g * b * g⁻¹ ∈ d.V.map L.subtype :=
      fun g hg b hb => (mem_normalizer_iff.1 (h.yamadaR₄_le_normalizer_V_R4 d hlay hg) b).1 hb
    have hle : yamadaR₄ d t ≤
        Common.centralizerMod (yamadaR₄ d t) (yamadaY₁ d t) (d.V.map L.subtype) hK hB := by
      refine h.yamadaR₄_le_of_le_R4 d hlay (fun r hr => ?_) (fun w hw => ?_) (fun m hm => ?_)
      · exact ⟨hR₂R₄ hr, fun y hy => comm_swap_mem_R4 (((E2 y).1 hy).2 r hr)⟩
      · refine ⟨h.yamadaW₃_le_yamadaR₄_R4 d hlay hw, fun y hy => mem_of_mul_comm_R4 ?_⟩
        exact (mem_centralizer_iff.1 (mem_inf.1 hw).2 y
          ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) (hY₁Y₂ hy))).symm
      · exact ⟨(mem_inf.1 hm).1, fun y hy => mem_of_mul_comm_R4
          (mem_centralizer_iff.1 (mem_inf.1 hm).2 y (hY₁Y₂ hy)).symm⟩
    refine ⟨hR₂R₄ hxR₂, fun y hy => ?_⟩
    exact comm_swap_mem_R4 ((Common.mem_centralizerMod.1 (hle hy)).2 x hx)
  · rintro ⟨hx, hc⟩
    have hVS₁ : d.V.map L.subtype ≤ yamadaS₁ d t :=
      ((V_le_yamadaV₁ d h562).trans (yamadaV₁_le_yamadaD₁ d t)).trans le_sup_right
    exact (E2 x).2 ⟨h.mem_yamadaR₂_of_commutator_mem_R4 d hlay hVS₁ hx hc,
      fun y hy => hc y (hR₂R₄ hy)⟩

theorem forall_mem_of_mem_yamadaW₂_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaW₂ d t) :
    x ∈ yamadaR₄ d t ∧ ∀ y ∈ yamadaR₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaY₁ d t := by
  layer_ctx
  obtain ⟨-, -, E3⟩ := h.series_yamadaR₂_R4 d hlay
  have hR₂R₄ := h.yamadaR₂_le_yamadaR₄_R4 d hlay
  have hY₂R₄ : yamadaY₂ d t ≤ yamadaR₄ d t :=
    (h.yamadaY₂_le_yamadaL₂_D1 d hlay).trans ((le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t).trans
      hR₂R₄)
  refine ⟨hR₂R₄ ((E3 x).1 (mem_sup_left hx)).1, fun y hy => ?_⟩
  have hB : ∀ g ∈ yamadaR₄ d t, ∀ b ∈ yamadaY₁ d t, g * b * g⁻¹ ∈ yamadaY₁ d t :=
    fun g hg b hb => (mem_normalizer_iff.1 (h.yamadaR₄_le_normalizer_yamadaY₁_R4 d hlay hg) b).1 hb
  have hK : ∀ g ∈ yamadaR₄ d t, ∀ y ∈ yamadaW₂ d t, g * y * g⁻¹ ∈ yamadaW₂ d t :=
    fun g hg y hy =>
      (mem_normalizer_iff.1 (h.yamadaR₄_le_normalizer_yamadaW₂_R4 d hlay hg) y).1 hy
  have hK' : ∀ g ∈ yamadaR₄ d t, ∀ y ∈ yamadaM₄ d t, g * y * g⁻¹ ∈ yamadaM₄ d t :=
    fun g hg y hy =>
      (mem_normalizer_iff.1 (h.yamadaR₄_le_normalizer_yamadaM₄_R4 d hlay hg) y).1 hy
  have hW₂K' : yamadaW₂ d t ≤ Common.centralizerMod (yamadaR₄ d t) (yamadaM₄ d t)
      (yamadaY₁ d t) hK' hB := by
    refine sup_le (fun w hw => ⟨h.S_map_le_yamadaR₄_R4 d hlay (map_mono d.W_le_S hw),
      fun m hm => ?_⟩) (fun a ha => ⟨hY₂R₄ ha, fun m hm => mem_of_mul_comm_R4 ?_⟩)
    · exact h.commutatorElement_mem_yamadaY₁ d hNH h561 h562 h591 h592 h593
        ((le_sup_left : d.W.map L.subtype ≤ yamadaW₁ d t) hw) (mem_inf.1 (mem_inf.1 hm).1).1
    · exact (mem_centralizer_iff.1 (mem_inf.1 hm).2 a ha)
  have hle : yamadaR₄ d t ≤ Common.centralizerMod (yamadaR₄ d t) (yamadaW₂ d t) (yamadaY₁ d t)
      hK hB := by
    refine h.yamadaR₄_le_of_le_R4 d hlay (fun r hr => ?_) (fun w hw => ?_) (fun m hm => ?_)
    · exact ⟨hR₂R₄ hr, fun y hy => comm_swap_mem_R4 (((E3 y).1 (mem_sup_left hy)).2 r hr)⟩
    · exact ⟨h.yamadaW₃_le_yamadaR₄_R4 d hlay hw, fun y hy =>
        mem_of_mul_comm_R4 (mem_centralizer_iff.1 (mem_inf.1 hw).2 y hy).symm⟩
    · exact ⟨(mem_inf.1 hm).1, fun y hy =>
        comm_swap_mem_R4 ((Common.mem_centralizerMod.1 (hW₂K' hy)).2 m hm)⟩
  exact comm_swap_mem_R4 ((Common.mem_centralizerMod.1 (hle hy)).2 x hx)

theorem mem_yamadaW₂_iff_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} :
    x ∈ yamadaW₂ d t ↔ x ∈ yamadaR₄ d t ∧
      ∀ y ∈ yamadaR₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaY₁ d t := by
  layer_ctx
  obtain ⟨-, -, E3⟩ := h.series_yamadaR₂_R4 d hlay
  have hR₂R₄ := h.yamadaR₂_le_yamadaR₄_R4 d hlay
  refine ⟨h.forall_mem_of_mem_yamadaW₂_R4 d hlay, ?_⟩
  rintro ⟨hxR₄, hc⟩
  have hY₁S₁ : yamadaY₁ d t ≤ yamadaS₁ d t := (yamadaY₁_le_yamadaD₁ d).trans le_sup_right
  have hxR₂ := h.mem_yamadaR₂_of_commutator_mem_R4 d hlay hY₁S₁ hxR₄ hc
  have hx3 := (E3 x).2 ⟨hxR₂, fun y hy => hc y (hR₂R₄ hy)⟩
  rcases (h.mem_sup_zpowers_iff_of_normalizer (h.t_mem_normalizer_yamadaW₂ d)).1 hx3 with h1 | h1
  · exact h1
  · exfalso
    have hK : ∀ g ∈ yamadaR₄ d t, ∀ y ∈ yamadaR₄ d t, g * y * g⁻¹ ∈ yamadaR₄ d t :=
      fun g hg y hy => mul_mem (mul_mem hg hy) (inv_mem hg)
    have hB : ∀ g ∈ yamadaR₄ d t, ∀ b ∈ yamadaY₁ d t, g * b * g⁻¹ ∈ yamadaY₁ d t :=
      fun g hg b hb =>
        (mem_normalizer_iff.1 (h.yamadaR₄_le_normalizer_yamadaY₁_R4 d hlay hg) b).1 hb
    have hxZ : x ∈ Common.centralizerMod (yamadaR₄ d t) (yamadaR₄ d t) (yamadaY₁ d t) hK hB :=
      ⟨hxR₄, hc⟩
    have htxZ : t * x ∈ Common.centralizerMod (yamadaR₄ d t) (yamadaR₄ d t) (yamadaY₁ d t) hK hB :=
      h.forall_mem_of_mem_yamadaW₂_R4 d hlay h1
    have htZ : t ∈ Common.centralizerMod (yamadaR₄ d t) (yamadaR₄ d t) (yamadaY₁ d t) hK hB := by
      have := mul_mem htxZ (inv_mem hxZ)
      rwa [mul_inv_cancel_right] at this
    obtain ⟨y₀, hy₀, hy₀R₃⟩ :=
      h.exists_mem_yamadaR₄_not_mem_yamadaR₃ d hNH h561 h562 h591 h592 h593
    apply hy₀R₃
    refine (h.mem_yamadaR₃_iff_of_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593 hy₀).2 ?_
    have h2 := htZ.2 y₀ hy₀
    rw [inv_eq_of_mul_eq_one_right h.t_mul_t] at h2
    exact yamadaY₁_le_yamadaW₁ d h2

end Series

section Characteristic

theorem yamadaY₂_le_yamadaM₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaY₂ d t ≤ yamadaM₄ d t :=
  le_inf ((h.yamadaY₂_le_yamadaL₂_D1 d hlay).trans
    ((le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t).trans (h.yamadaR₂_le_yamadaR₄_R4 d hlay)))
    fun y hy => mem_centralizer_iff.2 fun z hz => h.mul_comm_of_mem_yamadaY₂ d hlay hz hy

theorem yamadaW₃_le_yamadaM₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaW₃ d t ≤ yamadaM₄ d t :=
  le_inf (h.yamadaW₃_le_yamadaR₄_R4 d hlay) fun _ hx =>
    centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) (mem_inf.1 hx).2

theorem yamadaM₄_eq_inf_centralizer_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₄ d t = yamadaR₄ d t ⊓ centralizer (yamadaY₁ d t : Set G) := by
  layer_ctx
  have hY₁Y₂ := h.yamadaY₁_le_yamadaY₂ d hlay
  have hYY₁ : d.Y.map L.subtype ≤ yamadaY₁ d t := le_sup_left
  have hV₁Y₁ : yamadaV₁ d t ≤ yamadaY₁ d t := le_sup_right
  refine le_antisymm (inf_le_inf_left _ (centralizer_le hY₁Y₂)) (fun x hx => ?_)
  obtain ⟨hxR₄, hxC⟩ := mem_inf.1 hx
  have hxL₄ : x ∈ yamadaL₄ d t := mem_inf.2 ⟨hxR₄, centralizer_le hYY₁ hxC⟩
  have htM₄ : t ∈ normalizer (yamadaM₄ d t : Set G) :=
    h.yamadaR₄_le_normalizer_yamadaM₄_R4 d hlay
      (h.t_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593)
  rw [h524.1.1, h.mem_sup_zpowers_iff_of_normalizer htM₄] at hxL₄
  rcases hxL₄ with h1 | h1
  · exact h1
  · exfalso
    have h2 : t * x ∈ centralizer (yamadaV₁ d t : Set G) :=
      centralizer_le (yamadaV₁_le_yamadaY₂ d) (mem_inf.1 h1).2
    have h3 : x ∈ centralizer (yamadaV₁ d t : Set G) := centralizer_le hV₁Y₁ hxC
    have := mul_mem h2 (inv_mem h3)
    rw [mul_inv_cancel_right] at this
    exact h.t_not_mem_centralizer_yamadaV₁ d hlay this

theorem yamadaY₂_eq_inf_centralizer_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaY₂ d t = yamadaW₂ d t ⊓ centralizer (yamadaM₄ d t : Set G) := by
  layer_ctx
  refine le_antisymm (le_inf le_sup_right (le_centralizer_iff.1
    (inf_le_right : yamadaM₄ d t ≤ centralizer (yamadaY₂ d t : Set G)))) (fun x hx => ?_)
  obtain ⟨hxW₂, hxC⟩ := mem_inf.1 hx
  have hMM₄ : d.M.map L.subtype ≤ yamadaM₄ d t :=
    le_inf ((map_mono d.M_le_S).trans (h.S_map_le_yamadaR₄_R4 d hlay))
      (h.M_map_le_centralizer_yamadaY₂ d hlay)
  have hxM₂ : x ∈ yamadaM₂ d t :=
    (sup_le_sup_right (map_mono (d.W_le_F.trans d.F_le_M)) _ :
      yamadaW₂ d t ≤ yamadaM₂ d t) hxW₂
  have hM₂ : yamadaM₂ d t ≤ centralizer ({x} : Set G) := by
    refine sup_le (fun m hm => ?_) (fun y hy => ?_)
    · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxC m (hMM₄ hm))
    · exact mem_centralizer_singleton_iff.2
        (yamadaW₂_mul_comm d h592 ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hy) hxW₂)
  have hxC₂ : x ∈ centralizer (yamadaM₂ d t : Set G) :=
    mem_centralizer_iff.2 fun m hm => mem_centralizer_singleton_iff.1 (hM₂ hm)
  rw [← h592.2.2.2.1]
  exact mem_inf.2 ⟨hxM₂, hxC₂⟩

theorem normalizer_yamadaR₄_le_inf_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    normalizer (yamadaR₄ d t : Set G) ≤
      normalizer (yamadaY₂ d t : Set G) ⊓ normalizer (yamadaW₃ d t : Set G) := by
  layer_ctx
  intro g hg
  have hg₀ : g ∈ normalizer ((⊥ : Subgroup G) : Set G) :=
    mem_normalizer_fintype fun x hx => by
      rw [mem_bot.1 hx, mul_one, mul_inv_cancel]
      exact one_mem _
  have hgV : g ∈ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    mem_normalizer_of_forall_mem_iff_R4 hg hg hg₀ fun x => h.mem_yamadaV_iff_R4 d hlay
  have hgY₁ : g ∈ normalizer (yamadaY₁ d t : Set G) :=
    mem_normalizer_of_forall_mem_iff_R4 hg hg hgV fun x => h.mem_yamadaY₁_iff_R4 d hlay
  have hgW₂ : g ∈ normalizer (yamadaW₂ d t : Set G) :=
    mem_normalizer_of_forall_mem_iff_R4 hg hg hgY₁ fun x => h.mem_yamadaW₂_iff_R4 d hlay
  have hgM₄ : g ∈ normalizer (yamadaM₄ d t : Set G) := by
    rw [h.yamadaM₄_eq_inf_centralizer_R4 d hlay]
    exact Common.mem_normalizer_inf hg (mem_normalizer_centralizer_C8 hgY₁)
  have hgY₂ : g ∈ normalizer (yamadaY₂ d t : Set G) := by
    rw [h.yamadaY₂_eq_inf_centralizer_R4 d hlay]
    exact Common.mem_normalizer_inf hgW₂ (mem_normalizer_centralizer_C8 hgM₄)
  have hgF₃ : g ∈ normalizer (yamadaF₃ d t : Set G) := by
    have := normalizer_le_normalizer_commutator_C8 (yamadaR₄ d t) hg
    rwa [h524.2.2] at this
  have hgW₃ : g ∈ normalizer (yamadaW₃ d t : Set G) := by
    rw [h.yamadaW₃_eq_inf_centralizer_R4 d hlay]
    exact Common.mem_normalizer_inf hgF₃ (mem_normalizer_centralizer_C8 hgW₂)
  exact mem_inf.2 ⟨hgY₂, hgW₃⟩

end Characteristic

section Four

theorem t_mem_normalizer_yamadaS₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ normalizer (yamadaS₄ d t : Set G) := by
  layer_ctx
  exact Common.mem_normalizer_inf
    (le_normalizer (h.t_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593))
    (mem_normalizer_centralizer_C8
      (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d)))

theorem S_map_le_yamadaS₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.S.map L.subtype ≤ yamadaS₄ d t :=
  le_inf (h.S_map_le_yamadaR₄_R4 d hlay) (h.S_map_le_centralizer_yamadaV₁ d hlay)

theorem yamadaW₃_le_yamadaS₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaW₃ d t ≤ yamadaS₄ d t :=
  le_inf (h.yamadaW₃_le_yamadaR₄_R4 d hlay) fun _ hx =>
    centralizer_le (yamadaV₁_le_yamadaY₂ d)
      (centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) (mem_inf.1 hx).2)

theorem yamadaM₄_le_yamadaS₄_R4 {q : ℕ} (d : TrialityD4Data L q) (t : G) :
    yamadaM₄ d t ≤ yamadaS₄ d t :=
  inf_le_inf_left _ (centralizer_le (yamadaV₁_le_yamadaY₂ d))

theorem yamadaD₁_le_yamadaS₄_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaD₁ d t ≤ yamadaS₄ d t :=
  le_inf (h.yamadaD₁_le_yamadaR₄_R4 d hlay) (yamadaD₁_le_centralizer_yamadaV₁ d)

theorem yamadaS₄_eq_of_le_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {Q : Subgroup G} (hQ : Q ≤ yamadaS₄ d t)
    (htQ : t ∈ normalizer (Q : Set G)) (hR₄ : yamadaR₄ d t ≤ Q ⊔ zpowers t) :
    yamadaS₄ d t = Q := by
  refine le_antisymm (fun x hx => ?_) hQ
  obtain ⟨hxR₄, hxC⟩ := mem_inf.1 hx
  rcases (h.mem_sup_zpowers_iff_of_normalizer htQ).1 (hR₄ hxR₄) with h1 | h1
  · exact h1
  · exfalso
    have h3 : t * x ∈ centralizer (yamadaV₁ d t : Set G) := (mem_inf.1 (hQ h1)).2
    have := mul_mem h3 (inv_mem hxC)
    rw [mul_inv_cancel_right] at this
    exact h.t_not_mem_centralizer_yamadaV₁ d hlay this

theorem yamadaR₄_le_sup_zpowers_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaR₄ d t ≤ (d.S.map L.subtype ⊔ yamadaW₃ d t ⊔ yamadaM₄ d t) ⊔ zpowers t := by
  layer_ctx
  have hR₂ : yamadaR₂ d t ≤ (d.S.map L.subtype ⊔ yamadaW₃ d t ⊔ yamadaM₄ d t) ⊔ zpowers t := by
    refine sup_le ?_ ((le_sup_left.trans le_sup_left).trans le_sup_left)
    rw [h591.1]
    exact sup_le (sup_le ((map_mono d.M_le_S).trans
      ((le_sup_left.trans le_sup_left).trans le_sup_left))
      ((h.yamadaY₂_le_yamadaM₄_R4 d hlay).trans (le_sup_right.trans le_sup_left))) le_sup_right
  exact (h.yamadaR₄_le_sup_R4 d hlay).trans (sup_le (sup_le hR₂
    ((le_sup_right.trans le_sup_left).trans le_sup_left)) (le_sup_right.trans le_sup_left))

theorem yamadaS₄_eq_sup_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaS₄ d t = d.S.map L.subtype ⊔ yamadaW₃ d t ⊔ yamadaM₄ d t := by
  layer_ctx
  have hQ : d.S.map L.subtype ⊔ yamadaW₃ d t ⊔ yamadaM₄ d t ≤ yamadaS₄ d t :=
    sup_le (sup_le (h.S_map_le_yamadaS₄_R4 d hlay) (h.yamadaW₃_le_yamadaS₄_R4 d hlay))
      (yamadaM₄_le_yamadaS₄_R4 d t)
  have htS : t ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    h.t_mem_normalizer_map d.S
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.t_mem_normalizer_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have htM₄ : t ∈ normalizer (yamadaM₄ d t : Set G) :=
    h.yamadaR₄_le_normalizer_yamadaM₄_R4 d hlay (h.t_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593)
  have htQ : t ∈ normalizer
      ((d.S.map L.subtype ⊔ yamadaW₃ d t ⊔ yamadaM₄ d t : Subgroup G) : Set G) :=
    Common.mem_normalizer_sup (Common.mem_normalizer_sup htS htW₃) htM₄
  exact h.yamadaS₄_eq_of_le_R4 d hlay hQ htQ (h.yamadaR₄_le_sup_zpowers_R4 d hlay)

theorem mem_yamadaS₄_or_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaR₄ d t) :
    x ∈ yamadaS₄ d t ∨ t * x ∈ yamadaS₄ d t := by
  have hle : yamadaR₄ d t ≤ yamadaS₄ d t ⊔ zpowers t := by
    refine (h.yamadaR₄_le_sup_zpowers_R4 d hlay).trans (sup_le_sup_right ?_ _)
    rw [← h.yamadaS₄_eq_sup_R4 d hlay]
  exact (h.mem_sup_zpowers_iff_of_normalizer (h.t_mem_normalizer_yamadaS₄_R4 d hlay)).1 (hle hx)

theorem yamadaS₄_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaS₄ d t = yamadaM₄ d t ⊔ yamadaD₁ d t := by
  have hMM₄ : d.M.map L.subtype ≤ yamadaM₄ d t :=
    le_inf ((map_mono d.M_le_S).trans (h.S_map_le_yamadaR₄_R4 d hlay))
      (h.M_map_le_centralizer_yamadaY₂ d hlay)
  refine le_antisymm ?_ (sup_le (yamadaM₄_le_yamadaS₄_R4 d t) (h.yamadaD₁_le_yamadaS₄_R4 d hlay))
  rw [h.yamadaS₄_eq_sup_R4 d hlay]
  refine sup_le (sup_le ?_ ((h.yamadaW₃_le_yamadaM₄_R4 d hlay).trans le_sup_left)) le_sup_left
  rw [d.S_eq_sup, Subgroup.map_sup]
  exact sup_le (((map_mono d.U₁_le_M).trans hMM₄).trans le_sup_left)
    ((D_le_yamadaD₁ d t).trans le_sup_right)

theorem yamadaS₄_eq_sup_yamadaD₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaS₄ d t = yamadaM₄ d t ⊔ yamadaD₄ d t := by
  have hD₁D₄ : yamadaD₁ d t ≤ yamadaD₄ d t :=
    le_inf (h.yamadaD₁_le_yamadaR₄_R4 d hlay)
      (le_inf ((h.yamadaD₁_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t))
        (yamadaD₁_le_centralizer_yamadaV₁ d))
  have hD₄S₄ : yamadaD₄ d t ≤ yamadaS₄ d t :=
    inf_le_inf_left _ (inf_le_right : yamadaD₅ d t ≤ centralizer (yamadaV₁ d t : Set G))
  refine le_antisymm ?_ (sup_le (yamadaM₄_le_yamadaS₄_R4 d t) hD₄S₄)
  rw [h.yamadaS₄_eq_sup d hlay]
  exact sup_le_sup_left hD₁D₄ _

theorem commutator_mem_yamadaY₂_of_mem_yamadaS₄ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (hM₄ : ∀ m ∈ yamadaM₄ d t, ∀ w ∈ yamadaW₃ d t, m * w * m⁻¹ * w⁻¹ ∈ yamadaY₂ d t)
    {s w : G} (hs : s ∈ yamadaS₄ d t) (hw : w ∈ yamadaW₃ d t) :
    s * w * s⁻¹ * w⁻¹ ∈ yamadaY₂ d t := by
  layer_ctx
  have hK : ∀ g ∈ yamadaR₄ d t, ∀ y ∈ yamadaW₃ d t, g * y * g⁻¹ ∈ yamadaW₃ d t :=
    fun g hg y hy => (mem_normalizer_iff.1 (h.yamadaR₄_le_normalizer_yamadaW₃_R4 d hlay hg) y).1 hy
  have hB : ∀ g ∈ yamadaR₄ d t, ∀ b ∈ yamadaY₂ d t, g * b * g⁻¹ ∈ yamadaY₂ d t :=
    fun g hg b hb => (mem_normalizer_iff.1 (h.yamadaR₄_le_normalizer_yamadaY₂_R4 d hlay hg) b).1 hb
  have hle : yamadaS₄ d t ≤
      Common.centralizerMod (yamadaR₄ d t) (yamadaW₃ d t) (yamadaY₂ d t) hK hB := by
    rw [h.yamadaS₄_eq_sup d hlay]
    refine sup_le (fun m hm => ⟨(mem_inf.1 hm).1, fun w hw => hM₄ m hm w hw⟩)
      (fun δ hδ => ⟨h.yamadaD₁_le_yamadaR₄_R4 d hlay hδ, fun w hw => ?_⟩)
    have hδD₅ : δ ∈ yamadaD₅ d t :=
      mem_inf.2 (⟨(h.yamadaD₁_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t) hδ,
        yamadaD₁_le_centralizer_yamadaV₁ d hδ⟩)
    have hwD₅ : w ∈ yamadaD₅ d t :=
      mem_inf.2 ⟨h.yamadaW₃_le_yamadaC₅ d hlay hw,
        (mem_inf.1 (h.yamadaW₃_le_yamadaS₄_R4 d hlay hw)).2⟩
    have := commutator_mem_commutator hδD₅ hwD₅
    rw [h525.1] at this
    exact yamadaV₁_le_yamadaY₂ d this
  exact (Common.mem_centralizerMod.1 (hle hs)).2 w hw

theorem mem_yamadaS₄_iff_R4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hM₄ : ∀ m ∈ yamadaM₄ d t, ∀ w ∈ yamadaW₃ d t, m * w * m⁻¹ * w⁻¹ ∈ yamadaY₂ d t)
    {x : G} :
    x ∈ yamadaS₄ d t ↔ x ∈ yamadaR₄ d t ∧
      ∀ w ∈ yamadaW₃ d t, x * w * x⁻¹ * w⁻¹ ∈ yamadaY₂ d t := by
  layer_ctx
  refine ⟨fun hx => ⟨(mem_inf.1 hx).1, fun w hw =>
    h.commutator_mem_yamadaY₂_of_mem_yamadaS₄ d hlay hM₄ hx hw⟩, ?_⟩
  rintro ⟨hxR₄, hc⟩
  rcases h.mem_yamadaS₄_or_R4 d hlay hxR₄ with h1 | h1
  · exact h1
  · exfalso
    have hK : ∀ g ∈ yamadaR₄ d t, ∀ y ∈ yamadaW₃ d t, g * y * g⁻¹ ∈ yamadaW₃ d t :=
      fun g hg y hy =>
        (mem_normalizer_iff.1 (h.yamadaR₄_le_normalizer_yamadaW₃_R4 d hlay hg) y).1 hy
    have hB : ∀ g ∈ yamadaR₄ d t, ∀ b ∈ yamadaY₂ d t, g * b * g⁻¹ ∈ yamadaY₂ d t :=
      fun g hg b hb =>
        (mem_normalizer_iff.1 (h.yamadaR₄_le_normalizer_yamadaY₂_R4 d hlay hg) b).1 hb
    have hxZ : x ∈ Common.centralizerMod (yamadaR₄ d t) (yamadaW₃ d t) (yamadaY₂ d t) hK hB :=
      ⟨hxR₄, hc⟩
    have htxZ : t * x ∈
        Common.centralizerMod (yamadaR₄ d t) (yamadaW₃ d t) (yamadaY₂ d t) hK hB :=
      ⟨(mem_inf.1 h1).1, fun w hw => h.commutator_mem_yamadaY₂_of_mem_yamadaS₄ d hlay hM₄ h1 hw⟩
    have htZ : t ∈ Common.centralizerMod (yamadaR₄ d t) (yamadaW₃ d t) (yamadaY₂ d t) hK hB := by
      have := mul_mem htxZ (inv_mem hxZ)
      rwa [mul_inv_cancel_right] at this
    have hx₄ : ((d.x₄ 1 : L) : G) ∈ d.W.map L.subtype := ⟨_, d.x₄_mem_W 1, rfl⟩
    obtain ⟨w₀, hw₀, he⟩ := h.exists_mem_yamadaW₃_crossed_eq_C9 d hNH h561 h562 h591 h592 h593
      h5101 h5102 h521 hx₄
    have h2 := htZ.2 w₀ hw₀
    rw [inv_eq_of_mul_eq_one_right h.t_mul_t, he] at h2
    have h3 : ((d.x₄ 1 : L) : G) ∈ yamadaY₂ d t ⊓ centralizer ({t} : Set G) :=
      mem_inf.2 ⟨h2, h.L_le_centralizer (d.x₄ 1).2⟩
    rw [h592.2.2.2.2] at h3
    obtain ⟨y, hy, hye⟩ := h3
    rw [Subtype.ext hye] at hy
    exact one_ne_zero (d.x₄_mem_Y_iff.1 hy)

theorem normalizer_yamadaR₄_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hM₄ : ∀ m ∈ yamadaM₄ d t, ∀ w ∈ yamadaW₃ d t, m * w * m⁻¹ * w⁻¹ ∈ yamadaY₂ d t) :
    normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaS₄ d t : Set G) ⊓
      normalizer (yamadaW₃ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G) := by
  intro g hg
  obtain ⟨hgY₂, hgW₃⟩ := mem_inf.1 (h.normalizer_yamadaR₄_le_inf_R4 d hlay hg)
  exact mem_inf.2 ⟨mem_inf.2 ⟨mem_normalizer_of_forall_mem_iff_R4 hg hgW₃ hgY₂
    fun x => h.mem_yamadaS₄_iff_R4 d hlay hM₄, hgW₃⟩, hgY₂⟩

end Four

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
