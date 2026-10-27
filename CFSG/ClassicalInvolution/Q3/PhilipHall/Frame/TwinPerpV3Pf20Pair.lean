module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf10Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Fam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Lift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf4Layer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open scoped commutatorElement

section PairY


variable {n : ℕ} {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem liftPair_of_twinsY (hPerp : PerpHypS n G R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    {c : G} (hc2' : IsPGroup 2 (Subgroup.zpowers c)) (hcc : c * c = 1) (hc1 : c ≠ 1)
    {J J' : Subgroup G} (hJtq : J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) c)
    (hJ'tq : J' ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) c) (hJne : J' ≠ J)
    (htJ : IsUniqueInvolution J t) (htJ' : IsUniqueInvolution J' t)
    (htC : t ∈ Subgroup.centralizer ({c} : Set G))
    (lJ : TwinExitPf9.LiftedAtSec J c t htC) (lJ' : TwinExitPf9.LiftedAtSec J' c t htC)
    {x : G} (hxc : x ∈ Subgroup.centralizer ({c} : Set G))
    (hxJ : x ∈ centralizerModOdd ⊤ J) (hxJ' : x ∈ centralizerModOdd ⊤ J') :
    ∃ M M' : Subgroup G,
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M t ∧
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M' t ∧
      modOdd c M ≠ modOdd c M' ∧
      (∀ a ∈ modOdd c M, ∀ b ∈ modOdd c M', a * b = b * a) ∧
      (∀ a ∈ modOdd c M, oddQuotMk c ⟨x, hxc⟩ * a = a * oddQuotMk c ⟨x, hxc⟩) ∧
      (∀ a ∈ modOdd c M', oddQuotMk c ⟨x, hxc⟩ * a = a * oddQuotMk c ⟨x, hxc⟩) ∧
      (∀ g ∈ TwinADescent.coreAt c J, g * t = t * g → g ∈ M) ∧
      (∀ g ∈ TwinADescent.coreAt c J', g * t = t * g → g ∈ M') := by
  classical
  have ht2 : t * t = 1 := htJ.sq
  have hsq' : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨t, htC⟩ = 1 :=
    Subtype.ext ht2
  have hS := layer_q8Section hPerp hcc
  obtain ⟨htH₁, L0, hL0⟩ := TwinExitPf9.isLiftOf_of_liftedAtSec hΩ hc2' hS hJtq htJ htC lJ
  obtain ⟨htH₂, L0', hL0'⟩ := TwinExitPf9.isLiftOf_of_liftedAtSec hΩ hc2' hS hJ'tq htJ' htC lJ'
  have htcore : ∀ J₀ : Subgroup G, IsUniqueInvolution J₀ t → t ∈ TwinADescent.coreAt c J₀ := by
    intro J₀ hJ₀
    have hle : Subgroup.zpowers t ≤ J₀ ⊓ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.zpowers_le.mpr ⟨hJ₀.mem, htC⟩
    exact le_tightCore_of_isPGroup hle
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ht2)
      (Subgroup.mem_zpowers t)
  have htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      coreHull (CoreAssembly.conjClass (tightCore R)) c :=
    le_coreHull hJtq (Subgroup.mem_subgroupOf.mpr (htcore J htJ))
  have hinvJ := hL0.inv
  have hinvJ' := hL0'.inv
  have hne_img : secImg (CoreAssembly.conjClass (tightCore R)) c J ≠
      secImg (CoreAssembly.conjClass (tightCore R)) c J' := by
    intro heq
    have hΛ : HypOmegaGen (cFam (CoreAssembly.conjClass (tightCore R)) c) :=
      TwinADescent.hypOmegaGen_coreFamily hΩ hc2'
    have hcore_ne : (TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G)) ≠
        (TwinADescent.coreAt c J').subgroupOf (Subgroup.centralizer ({c} : Set G)) := by
      intro he
      have := congrArg (Subgroup.map (Subgroup.centralizer ({c} : Set G)).subtype) he
      rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J),
        Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J')] at this
      exact hJne (eq_of_coreAt_eq hΩ hc2' hJtq hJ'tq this).symm
    exact TwinExitPf2.false_of_imgOf_eq hΛ
      ⟨TwinADescent.coreAt c J, TwinADescent.coreAt_mem_coreFamily hJtq,
        TwinADescent.coreAt_le_centralizer c J, rfl⟩
      ⟨TwinADescent.coreAt c J', TwinADescent.coreAt_mem_coreFamily hJ'tq,
        TwinADescent.coreAt_le_centralizer c J', rfl⟩
      hcore_ne
      (isUniqueInvolution_subgroupOf
        (isUniqueInvolution_coreAt_of_tq hΩ hc2' hJtq htJ)
        (TwinADescent.coreAt_le_centralizer c J))
      (isUniqueInvolution_subgroupOf
        (isUniqueInvolution_coreAt_of_tq hΩ hc2' hJ'tq htJ')
        (TwinADescent.coreAt_le_centralizer c J'))
      (le_coreHull hJtq) (le_coreHull hJ'tq) heq
  obtain ⟨hJ2, hJ'2, L₁, L₂, hL₁, hL₂, hJL₁, hJL₂, hLne, hcomm, hfix₁, hfix₂⟩ :=
    TwinExitPf10.exists_lifted_pair_Y (CoreData.of_S hPerp.core).below hS.hyp hS.two hS.q8 (card_layer_lt hPerp hc1) hS.oddFree
      (secImg_mem_secFam hJtq) (secImg_mem_secFam hJ'tq) hne_img hinvJ hinvJ' ⟨L0, hL0⟩ ⟨L0', hL0'⟩
      (secAut (CoreAssembly.conjClass (tightCore R)) c hΩ hc2' ⟨x, hxc⟩)
      (fun K hK => TwinExitPf10.secAut_map_secFam hΩ hc2' ⟨x, hxc⟩ hK)
      (fun hP => secAut_fix_secImg hΩ hc2' hP hxc hxJ)
      (fun hP => secAut_fix_secImg hΩ hc2' hP hxc hxJ')
  have hH : IsSubnormal (coreHull (CoreAssembly.conjClass (tightCore R)) c) ⊤ := by
    haveI := normal_coreHull hΩ hc2'
    exact isSubnormal_of_normal_subgroupOf le_top inferInstance
  obtain ⟨M₁, hM₁, hM₁a, hM₁b, hM₁c⟩ :=
    exists_sectionMember_of_lift3 hH (t := ⟨t, htC⟩) htH hsq' hL₁
  obtain ⟨M₂, hM₂, hM₂a, hM₂b, hM₂c⟩ :=
    exists_sectionMember_of_lift3 hH (t := ⟨t, htC⟩) htH hsq' hL₂
  have hmem₁ := fun a => mem_modOdd_iff_of_lift hΩ hc2' hM₁a hM₁b (a := a)
  have hmem₂ := fun a => mem_modOdd_iff_of_lift hΩ hc2' hM₂a hM₂b (a := a)
  refine ⟨M₁, M₂, hM₁, hM₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    have inc : ∀ l ∈ L₁, l ∈ L₂ := by
      intro l hl1
      have h1 : secMap _ c hΩ hc2' l ∈ modOdd c M₁ := (hmem₁ _).2 ⟨l, hl1, rfl⟩
      rw [heq] at h1
      obtain ⟨l₂, hl₂, he⟩ := (hmem₂ _).1 h1
      rw [← secMap_injective hΩ hc2' he]
      exact hl₂
    have inc' : ∀ l ∈ L₂, l ∈ L₁ := by
      intro l hl2
      have h1 : secMap _ c hΩ hc2' l ∈ modOdd c M₂ := (hmem₂ _).2 ⟨l, hl2, rfl⟩
      rw [← heq] at h1
      obtain ⟨l₁, hl₁, he⟩ := (hmem₁ _).1 h1
      rw [← secMap_injective hΩ hc2' he]
      exact hl₁
    exact hLne (le_antisymm inc inc')
  · intro a ha b hb
    obtain ⟨l₁, hl₁, rfl⟩ := (hmem₁ a).1 ha
    obtain ⟨l₂, hl₂, rfl⟩ := (hmem₂ b).1 hb
    rw [← map_mul, ← map_mul, hcomm l₁ hl₁ l₂ hl₂]
  · intro a ha
    obtain ⟨l₁, hl₁, rfl⟩ := (hmem₁ a).1 ha
    exact oddQuot_centralizes_of_fix hΩ hc2' ⟨x, hxc⟩ hfix₁ hl₁
  · intro a ha
    obtain ⟨l₂, hl₂, rfl⟩ := (hmem₂ a).1 ha
    exact oddQuot_centralizes_of_fix hΩ hc2' ⟨x, hxc⟩ hfix₂ hl₂
  · intro g hg hgt
    have hgC := TwinADescent.coreAt_le_centralizer c J hg
    have hgH : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
        coreHull (CoreAssembly.conjClass (tightCore R)) c :=
      le_coreHull hJtq (Subgroup.mem_subgroupOf.mpr hg)
    exact hM₁c ⟨⟨g, hgC⟩, hgH⟩ (hJL₁ ⟨⟨⟨g, hgC⟩, hgH⟩, hg, rfl⟩) (Subtype.ext hgt)
  · intro g hg hgt
    have hgC := TwinADescent.coreAt_le_centralizer c J' hg
    have hgH : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
        coreHull (CoreAssembly.conjClass (tightCore R)) c :=
      le_coreHull hJ'tq (Subgroup.mem_subgroupOf.mpr hg)
    exact hM₂c ⟨⟨g, hgC⟩, hgH⟩ (hJL₂ ⟨⟨⟨g, hgC⟩, hgH⟩, hg, rfl⟩) (Subtype.ext hgt)

end PairY

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
