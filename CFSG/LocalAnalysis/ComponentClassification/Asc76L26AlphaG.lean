module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Alpha26
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Lemma27
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Borel

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding
open CFSG.ShultStronglyClosedTI

theorem IsSzOrU3.of_mulEquiv {X X' : Type*} [Group X] [Group X'] (h : IsSzOrU3 X')
    (e : X ≃* X') : IsSzOrU3 X := by
  rcases h with ⟨a, ha, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩
  · exact Or.inl ⟨a, ha, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨f, hf, ⟨e.trans e'⟩⟩

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {𝒯 : Set (Subgroup G)}
  {R : Subgroup G}

theorem alpha26 (h : Hyp26 S 𝒯 R) (hH : fusionGen (memberSet 𝒯) ≠ ⊤)
    (hO : CFSG.oddCore G = ⊥) (hZ : ∀ c ∈ center G, orderOf c ≠ 2) {a : G} (haR : a ∈ R)
    (ha2 : orderOf a = 2)
    (hpuc : ProductUniqueContainment (fusionGen (memberSet 𝒯)) a) :
    (∀ R' ∈ 𝒯, IsBig R' → R' = R) ∧ IsSylowOf 2 R (normalClosure (R : Set G)) ∧
      IsSzOrU3 (↥(normalClosure (R : Set G)) ⧸
        CFSG.Assembly.oddCore ↥(normalClosure (R : Set G))) ∧ SylowShape R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Γ := memberSet 𝒯 with hΓdef
  set H := fusionGen Γ with hHdef
  have hΓS : Γ ⊆ S := memberSet_subset h.toHypCore
  have ha1 : a ≠ 1 := fun h' => by rw [h', orderOf_one] at ha2; omega
  have haΓ : a ∈ Γ := mem_memberSet h.mem haR ha1
  have huniq := mem_rightConjugate_fusionGen_iff h.sylow h.closed hΓS haΓ
  obtain ⟨hLn, hLB, hse, hrank, haL⟩ := exists_normal_bender hO hZ hH ha2 huniq hpuc
  set L := involutionPointHull a with hLdef
  have hLs : IsSimpleGroup L :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hLB
  obtain ⟨T₀, hT₀⟩ := Lemma34.eq_normalizer_of_stronglyEmbedded hLs hse hrank
  have hCL : ∀ γ ∈ Γ, γ ∉ centralizer (L : Set G) := by
    intro γ hγ hγC
    apply hH
    refine fusionGen_eq_top_of_normal h.sylow h.closed hΓS hLn (fun x hx => ?_) haΓ haL
    exact centralizer_le_fusionGen hγ
      (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hγC x hx))
  set Y := L ⊔ S with hYdef
  have hLY : L ≤ Y := le_sup_left
  have hSY : S ≤ Y := le_sup_right
  have hRY : R ≤ Y := (h.le R h.mem).trans hSY
  set K := L.subgroupOf Y with hKdef
  have : K.Normal := Subgroup.Normal.subgroupOf hLn Y
  have hKB : fusionIsBenderGroup K :=
    fusionIsBenderGroup_congr (subgroupOfEquivOfLe hLY).symm hLB
  obtain ⟨P, hP⟩ := (h.sylow.of_le hSY le_top).exists_sylow_eq_subgroupOf
  have hKP : K ⊔ (P : Subgroup Y) = ⊤ := by
    rw [hP, ← subgroupOf_sup hLY hSY, subgroupOf_self]
  have hle : ∀ T ∈ subFamily Y 𝒯, T ≤ (P : Subgroup Y) := by
    rintro _ ⟨T, hT, rfl⟩
    rw [hP]
    exact fun x hx => mem_subgroupOf.mpr (h.le T hT (mem_subgroupOf.mp hx))
  have hcomm : ∀ T₁ ∈ subFamily Y 𝒯, ∀ T₂ ∈ subFamily Y 𝒯, T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥ := by
    rintro _ ⟨T₁, hT₁, rfl⟩ _ ⟨T₂, hT₂, rfl⟩ hne
    exact commutator_subgroupOf_eq_bot (h.comm T₁ hT₁ T₂ hT₂ fun h' => hne (by rw [h']))
  have hcl : fusionStronglyClosed (memberSet (subFamily Y 𝒯)) (P : Subgroup Y) := by
    intro x hx y hy
    rw [mem_memberSet_subFamily] at hx ⊢
    rw [hP, mem_subgroupOf] at hy
    simpa using h.closed _ hx y (by simpa using hy)
  have hRYm : R.subgroupOf Y ∈ subFamily Y 𝒯 := ⟨R, h.mem, rfl⟩
  have hbigY : IsBig (R.subgroupOf Y) := h.big.of_mulEquiv (subgroupOfEquivOfLe hRY).symm
  have hCY : ∀ γ ∈ memberSet (subFamily Y 𝒯), γ ∉ centralizer (K : Set Y) := by
    intro γ hγ hγC
    rw [mem_memberSet_subFamily] at hγ
    apply hCL _ hγ
    rw [mem_centralizer_iff]
    intro x hx
    have := mem_centralizer_iff.mp hγC ⟨x, hLY hx⟩ (mem_subgroupOf.mpr hx)
    exact congrArg Subtype.val this
  let e : L ≃* K := (subgroupOfEquivOfLe hLY).symm
  have he : ∀ x : L, ((e x : Y) : G) = x := fun _ => rfl
  have houtY : ∃ T₀' : Sylow 2 K, ∀ γ ∈ memberSet (subFamily Y 𝒯), ∀ x : K, γ * x * γ⁻¹ = x →
      x ∈ normalizer ((T₀' : Subgroup K) : Set K) := by
    have hes : Function.Surjective e.toMonoidHom := e.surjective
    refine ⟨T₀.mapSurjective hes, fun γ hγ x hx => ?_⟩
    rw [mem_memberSet_subFamily] at hγ
    rw [Sylow.coe_mapSurjective hes T₀, ← map_equiv_normalizer_eq]
    refine ⟨e.symm x, ?_, by simp⟩
    rw [← hT₀, SetLike.mem_coe, mem_subgroupOf]
    have hx' : ((e.symm x : L) : G) = ((x : Y) : G) := by
      rw [← he (e.symm x), MulEquiv.apply_symm_apply]
    rw [hx']
    apply centralizer_le_fusionGen hγ
    rw [mem_centralizer_singleton_iff]
    have := congrArg Subtype.val hx
    simp only [coe_mul, coe_inv] at this
    calc ((x : Y) : G) * (γ : G) = (γ : G) * ((γ : G)⁻¹ * (x : G) * γ) := by group
      _ = (γ : G) * ((γ : G)⁻¹ * ((γ : G) * (x : G) * (γ : G)⁻¹) * γ) := by rw [this]
      _ = (γ : G) * (x : G) := by group
  have haY : (⟨a, hLY haL⟩ : Y) ∈ R.subgroupOf Y := mem_subgroupOf.mpr haR
  have haK : (⟨a, hLY haL⟩ : Y) ∈ K := mem_subgroupOf.mpr haL
  have ha2Y : orderOf (⟨a, hLY haL⟩ : Y) = 2 := by rw [Subgroup.orderOf_mk]; exact ha2
  obtain ⟨hRT, huniqY, hSzK, hshapeY⟩ :=
    alpha26_core hKB P hKP hle hcomm hcl hRYm hbigY hCY houtY haY haK ha2Y
  have hRSL : R = S ⊓ L := by
    ext x
    constructor
    · intro hx
      have hxY : (⟨x, hRY hx⟩ : Y) ∈ R.subgroupOf Y := mem_subgroupOf.mpr hx
      rw [hRT, hP] at hxY
      exact mem_inf.mpr ⟨mem_subgroupOf.mp (mem_inf.mp hxY).1,
        mem_subgroupOf.mp (mem_inf.mp hxY).2⟩
    · intro hx
      have hxY : (⟨x, hSY (mem_inf.mp hx).1⟩ : Y) ∈ (P : Subgroup Y) ⊓ K := by
        rw [hP]
        exact mem_inf.mpr ⟨mem_subgroupOf.mpr (mem_inf.mp hx).1,
          mem_subgroupOf.mpr (mem_inf.mp hx).2⟩
      rw [← hRT] at hxY
      exact mem_subgroupOf.mp hxY
  have hRL : R ≤ L := hRSL ▸ inf_le_right
  have hnc : normalClosure (R : Set G) = L := by
    refine le_antisymm (normalClosure_le_normal hRL) ?_
    rw [hLdef, involutionPointHull, closure_le]
    rintro _ ⟨g, rfl⟩
    have := (normalClosure_normal (s := (R : Set G))).conj_mem a
      (subset_normalClosure haR) g⁻¹
    simpa [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem] using this
  refine ⟨fun R' hR' hbig' => ?_, ?_, ?_, ?_⟩
  ·
    have hR'Y : R' ≤ Y := (h.le R' hR').trans hSY
    have h1 := huniqY _ ⟨R', hR', rfl⟩ (hbig'.of_mulEquiv (subgroupOfEquivOfLe hR'Y).symm)
    rw [subgroupOf_inj, inf_eq_left.mpr hR'Y, inf_eq_left.mpr hRY] at h1
    exact h1
  · rw [hnc, hRSL]
    exact h.sylow.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hLn])
  · rw [hnc]
    have hOL : CFSG.Assembly.oddCore L = ⊥ := Lemma34.oddCore_eq_bot_of_normal' hO L
    exact IsSzOrU3.of_mulEquiv hSzK
      ((QuotientGroup.quotientMulEquivOfEq hOL).trans (QuotientGroup.quotientBot.trans e))
  · exact hshapeY.of_mulEquiv (subgroupOfEquivOfLe hRY)

end CFSG.ComponentClassification.Asc76.L26
