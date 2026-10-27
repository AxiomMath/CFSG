module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43Cfg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotThm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf17Inst

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

section Restrict

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem subgroupOf_pairNormalizers_le {Y K J : Subgroup G} (hKY : K ≤ Y) (hJY : J ≤ Y)
    (zK zJ : Y) :
    (pairNormalizers K J (zK : G) (zJ : G)).subgroupOf Y ≤
      pairNormalizers (K.subgroupOf Y) (J.subgroupOf Y) zK zJ := by
  have hZ : (Subgroup.closure ({zK, zJ} : Set Y)).map Y.subtype =
      Subgroup.closure ({(zK : G), (zJ : G)} : Set G) :=
    map_closure_pair_subtype zK zJ
  have hZY : Subgroup.closure ({(zK : G), (zJ : G)} : Set G) ≤ Y := by
    rw [← hZ]
    exact Subgroup.map_subtype_le _
  have hN : ∀ {A : Subgroup G}, A ≤ Y →
      (A ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK : G), (zJ : G)} : Set G) :
        Subgroup G) : Set G)).subgroupOf Y ≤
        A.subgroupOf Y ⊓ Subgroup.normalizer
          ((Subgroup.closure ({zK, zJ} : Set Y) : Subgroup Y) : Set Y) := by
    intro A _ x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hx.1, ?_⟩
    have := (mem_normalizer_subgroupOf_iff hZY).mp hx.2
    rwa [← hZ, subgroupOf_map_subtype'] at this
  unfold pairNormalizers
  rw [Subgroup.subgroupOf_sup (inf_le_left.trans hKY) (inf_le_left.trans hJY)]
  exact sup_le_sup (hN hKY) (hN hJY)

variable [Finite G]

theorem aViol_of_restrict_gen (hΩ : HypOmegaGen Ω) {Y K J : Subgroup G} {zK zJ : Y}
    (hKY : K ≤ Y) (hJY : J ≤ Y)
    (hv : AViol (restrictFamily Ω Y) (K.subgroupOf Y) (J.subgroupOf Y) zK zJ) :
    AViol Ω K J (zK : G) (zJ : G) := by
  have hstar : J ∈ omegaStarNbr Ω K := omegaStarNbr_of_restrict hKY hJY hv.star
  refine ⟨hstar, fun h => hv.not_nbr ?_, isUniqueInvolution_of_subgroupOf hv.hzK hKY,
    isUniqueInvolution_of_subgroupOf hv.hzJ hJY, ?_⟩
  · exact E187C.omegaNbr_subgroupOf_of
      (fun hJ hT hTJ => Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJ hT hTJ) hKY hJY hstar.1 h
  · intro g hg hcon
    have hgY : g ∈ Y := by
      have : pairNormalizers K J (zK : G) (zJ : G) ≤ Y :=
        sup_le (inf_le_left.trans hKY) (inf_le_left.trans hJY)
      exact this hg
    refine hv.no_conj ⟨g, hgY⟩
      (subgroupOf_pairNormalizers_le hKY hJY zK zJ (Subgroup.mem_subgroupOf.mpr hg)) ?_
    rw [conjSub_subgroupOf Y ⟨g, hgY⟩ K]
    exact congrArg (fun M : Subgroup G => M.subgroupOf Y) hcon

theorem aGraphAdj_map_subtype_of_restrict (hΩ : HypOmegaGen Ω) {Y : Subgroup G}
    {B C : Subgroup Y} (h : aGraphAdj (restrictFamily Ω Y) B C) :
    aGraphAdj Ω (B.map Y.subtype) (C.map Y.subtype) := by
  have hB : (B.map Y.subtype).subgroupOf Y = B := subgroupOf_map_subtype' B
  have hC : (C.map Y.subtype).subgroupOf Y = C := subgroupOf_map_subtype' C
  have hBY : B.map Y.subtype ≤ Y := Subgroup.map_subtype_le B
  have hCY : C.map Y.subtype ≤ Y := Subgroup.map_subtype_le C
  obtain ⟨hCΦ, ⟨zb, zc, hv⟩ | ⟨zc, zb, hv⟩ | ⟨⟨-, w, hwB, hwC⟩, hne⟩⟩ := h
  · rw [← hB, ← hC] at hv
    exact ⟨mem_restrictFamily_iff.mp hCΦ, Or.inl ⟨_, _, aViol_of_restrict_gen hΩ hBY hCY hv⟩⟩
  · rw [← hB, ← hC] at hv
    exact ⟨mem_restrictFamily_iff.mp hCΦ,
      Or.inr (Or.inl ⟨_, _, aViol_of_restrict_gen hΩ hCY hBY hv⟩)⟩
  · refine ⟨mem_restrictFamily_iff.mp hCΦ, Or.inr (Or.inr ⟨⟨mem_restrictFamily_iff.mp hCΦ,
      (w : G), isUniqueInvolution_map_of_inj Y.subtype_injective hwB,
      isUniqueInvolution_map_of_inj Y.subtype_injective hwC⟩, fun e => hne ?_⟩)⟩
    exact Subgroup.map_injective Y.subtype_injective e

theorem mem_aStar_of_restrict_gen (hΩ : HypOmegaGen Ω) {Y K : Subgroup G} (hKY : K ≤ Y)
    {L' : Subgroup Y} (h : L' ∈ aStar (restrictFamily Ω Y) (K.subgroupOf Y)) :
    L'.map Y.subtype ∈ aStar Ω K := by
  induction h with
  | refl =>
    rw [Subgroup.map_subgroupOf_eq_of_le hKY]
    exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (aGraphAdj_map_subtype_of_restrict hΩ hbc)

theorem mem_conjStab_aStar_of_conjSub_mem (hΩ : ConjInvariant Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {x : G} (hx : conjSub x K ∈ aStar Ω K) : x ∈ conjStab (aStar Ω K) := by
  have hinv : conjSub x⁻¹ K ∈ aStar Ω K := by
    have h := aStar_conj hΩ (mem_aStar_symm hK hx).2 x⁻¹
    rwa [conjSub_inv_conjSub] at h
  refine mem_conjStab_iff.mpr fun M => ⟨fun h => ?_, fun hM => hx.trans (aStar_conj hΩ hM x)⟩
  have h' := aStar_conj hΩ h x⁻¹
  rw [conjSub_inv_conjSub] at h'
  exact hinv.trans h'

theorem mem_conjStab_aStar_of_restrict (hΩ : HypOmegaGen Ω) {Y K : Subgroup G} (hK : K ∈ Ω)
    (hKY : K ≤ Y) {x : Y} (hx : x ∈ conjStab (aStar (restrictFamily Ω Y) (K.subgroupOf Y))) :
    (x : G) ∈ conjStab (aStar Ω K) := by
  have h1 : conjSub x (K.subgroupOf Y) ∈ aStar (restrictFamily Ω Y) (K.subgroupOf Y) :=
    (mem_conjStab_iff.mp hx _).mpr Relation.ReflTransGen.refl
  have hle : conjSub (x : G) K ≤ Y := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have h := Y.mul_mem (Y.mul_mem x.2 (hKY hy)) (Y.inv_mem x.2)
    simpa [mul_assoc] using h
  have h2 := mem_aStar_of_restrict_gen hΩ hKY h1
  rw [conjSub_subgroupOf, Subgroup.map_subgroupOf_eq_of_le hle] at h2
  exact mem_conjStab_aStar_of_conjSub_mem hΩ.conjInvariant hK h2

end Restrict

section Setup

variable {T : Type} [Group T] [Finite T]
  {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}

theorem frame_hs_stab_proved (hs : FrameStd K z J zJ) (hσ : sigmaOf K ≠ CoreAssembly.conjClass K) :
    sigmaGen K ≤ conjStab (aStar (CoreAssembly.conjClass K) K) := by
  have hΩg : HypOmegaGen (CoreAssembly.conjClass K) := hs.datum.hyp
  have hΩc : ConjInvariant (CoreAssembly.conjClass K) := hΩg.conjInvariant
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKH : K ≤ sigmaGen K := le_omegaGen (Relation.ReflTransGen.refl : K ∈ sigmaOf K)
  have hJA : J ∈ aStar (CoreAssembly.conjClass K) K :=
    Relation.ReflTransGen.single ⟨hs.viol.mem, Or.inl ⟨z, zJ, hs.viol⟩⟩
  have hJH : J ≤ sigmaGen K := le_omegaGen (aStar_subset_dstarComp_gen hΩg hK hJA).2
  have hHtop : sigmaGen K ≠ ⊤ := sigmaGen_ne_top hΩc hσ
  have hlt : Nat.card ↥(sigmaGen K) < Nat.card T :=
    lt_of_le_of_ne (Subgroup.card_le_card_group _)
      (fun h => hHtop ((Subgroup.card_eq_iff_eq_top _).mp h))
  set Φ := restrictFamily (CoreAssembly.conjClass K) (sigmaGen K) with hΦ_def
  set K' := K.subgroupOf (sigmaGen K) with hK'_def
  have hΦ : TypeRHyp Φ := (typeRHyp_of_datum hs.datum).restrict (sigmaGen K)
  have hKΦ : K' ∈ Φ := subgroupOf_mem_restrictFamily hK hKH
  have hnA : ¬ AEmpty Φ K' :=
    not_aEmpty_iff.mpr ⟨J.subgroupOf (sigmaGen K), _, _, aViol_restrict_gen hΩg hKH hJH hs.viol⟩
  have hQ := Thm3A.thm3RGroupQuotG_of_belowG hs.below hlt
  refine iSup₂_le fun L hL => ?_
  have hLΩ : L ∈ CoreAssembly.conjClass K := (mem_dstarComp_symm hK hL).1
  have hLH : L ≤ sigmaGen K := le_omegaGen hL
  by_cases hLA : L.subgroupOf (sigmaGen K) ∈ aStar Φ K'
  · have h1 := mem_aStar_of_restrict_gen hΩg hKH hLA
    rw [Subgroup.map_subgroupOf_eq_of_le hLH] at h1
    exact le_conjStab_aStar hΩc hK h1
  · have hst := (Thm3A.thm3R_lift_stab hQ hΦ hKΦ hnA (subgroupOf_mem_restrictFamily hLΩ hLH) hLA
      (Relation.ReflTransGen.refl : K' ∈ aStar Φ K')).1
    intro x hx
    exact mem_conjStab_aStar_of_restrict hΩg hK hKH (x := ⟨x, hLH hx⟩)
      (hst (Subgroup.mem_subgroupOf.mpr hx))

end Setup

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
