module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentInitial.OddProjectivePairExclusion

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup Matrix CFSG.ComponentClassification

universe u

theorem isComponentOf_of_normal_inf {G : Type*} [Group G] {T H B : Subgroup G} (hT : T.Normal)
    (hB : CFSG.Assembly.IsComponentOf B (T ⊓ H)) : CFSG.Assembly.IsComponentOf B H := by
  refine ⟨hB.1.trans inf_le_right, assembly_isSubnormal_trans hB.2.1
    (CFSG.Assembly.IsSubnormal.step inf_le_right ?_ (CFSG.Assembly.IsSubnormal.refl H)), hB.2.2⟩
  rw [inf_subgroupOf_right]
  exact hT.subgroupOf H

theorem range_toPGL_normal (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
    (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)).range.Normal := by
  have h : (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)).range =
      (SpecialLinearGroup.toGL (n := n) (R := R)).range.map ProjGenLinGroup.mk := by
    rw [MonoidHom.map_range]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      induction y using QuotientGroup.induction_on with
      | H A => exact ⟨A, rfl⟩
    · rintro ⟨A, rfl⟩
      exact ⟨QuotientGroup.mk A, rfl⟩
  rw [h, SpecialLinearGroup.range_toGL_eq_ker_det]
  exact (GeneralLinearGroup.det.normal_ker).map _ ProjGenLinGroup.mk_surjective

theorem card_map_mk'_center_of_sq_eq_one {G : Type*} [Group G] {L : Subgroup G}
    (hodd : Odd (Nat.card (center L))) {W : Subgroup L} (hW : ∀ w ∈ W, w ^ 2 = 1) :
    Nat.card (W.map (QuotientGroup.mk' (center L))) = Nat.card W := by
  have hinj : Set.InjOn (QuotientGroup.mk' (center L)) (W : Set L) := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ center L := QuotientGroup.eq.1 hxy
    have h1 : orderOf (x⁻¹ * y) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (hW _ (W.mul_mem (W.inv_mem hx) hy))
    have h2 : orderOf (x⁻¹ * y) ∣ Nat.card (center L) := by
      have := orderOf_dvd_natCard (⟨x⁻¹ * y, hz⟩ : center L)
      rwa [Subgroup.orderOf_mk] at this
    exact inv_mul_eq_one.1 (orderOf_eq_one_iff.1
      (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hodd) h1 h2))
  have := Nat.card_image_of_injOn hinj
  rwa [← Subgroup.coe_map] at this

theorem exists_four_group_centerQuotientImage {G : Type*} [Group G] {J K L : Subgroup G}
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJK : IsConjOf J K) (hKL : K ≤ L) (hodd : Odd (Nat.card (center L))) :
    ∃ V : Subgroup (L ⧸ center L), V ≤ centerQuotientImage L K ∧
      CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVJ, hVe, hVc⟩ := hV
  obtain ⟨g, rfl⟩ := hJK
  have hV'K : conjSub g V ≤ conjSub g J := Subgroup.map_mono hVJ
  have hV'L : conjSub g V ≤ L := hV'K.trans hKL
  have : CFSG.IsElementaryAbelian 2 (conjSub g V) := CFSG.IsElementaryAbelian.map _
  have hWe : CFSG.IsElementaryAbelian 2 ((conjSub g V).subgroupOf L) :=
    CFSG.IsElementaryAbelian.subgroupOf hV'L
  refine ⟨((conjSub g V).subgroupOf L).map (QuotientGroup.mk' (center L)),
    Subgroup.map_mono fun x hx => hV'K hx, CFSG.IsElementaryAbelian.map _, ?_⟩
  rw [card_map_mk'_center_of_sq_eq_one hodd
      fun w hw => CFSG.elemPow_eq_one_of_isElementaryAbelian w hw,
    Nat.card_congr (subgroupOfEquivOfLe hV'L).toEquiv, card_conjSub, hVc]

theorem commuting_block_odd_projective_linear_overgroup_exclusion {G : Type*} [Group G]
    [Finite G] {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J)
    (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ∀ (n : ℕ) (k : Type u) [Field k] [Finite k], 2 ≤ n → ringChar k ≠ 2 →
      ¬ Nonempty (L ⧸ center L ≃* ProjectiveSpecialLinearGroup (Fin n) k) := by
  intro n k _ _ hn hk ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  let ψ : L ⧸ center L →* ProjGenLinGroup (Fin n) k :=
    ProjectiveSpecialLinearGroup.toPGL.comp e.toMonoidHom
  have hψ : Function.Injective ψ :=
    ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective
  have hψrange : ψ.range.Normal := by
    have h : ψ.range = (ProjectiveSpecialLinearGroup.toPGL (n := Fin n) (R := k)).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map]
    rw [h]
    exact range_toPGL_normal (Fin n) k
  have hfour : ∀ K ∈ block J, ∃ V : Subgroup (ProjGenLinGroup (Fin n) k),
      V ≤ (centerQuotientImage L K).map ψ ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
    intro K hK
    obtain ⟨V, hVK, hVe, hVc⟩ :=
      exists_four_group_centerQuotientImage hV hK.1 ((le_blockGroup hK).trans hML) hodd
    exact ⟨V.map ψ, Subgroup.map_mono hVK, CFSG.IsElementaryAbelian.map ψ,
      by rw [Subgroup.card_map_of_injective hψ, hVc]⟩
  have hlocal : ∀ K ∈ block J, ∀ K' ∈ block J, K ≠ K' →
      ∀ t ∈ (centerQuotientImage L K').map ψ, orderOf t = 2 →
        CFSG.Assembly.IsComponentOf ((centerQuotientImage L K).map ψ)
          (centralizer ({t} : Set (ProjGenLinGroup (Fin n) k))) := by
    intro K hK K' hK' hKK' t ht ht2
    obtain ⟨w, hw, rfl⟩ := ht
    rw [orderOf_injective ψ hψ] at ht2
    obtain ⟨t₀, ht₀K, ht₀2, rfl⟩ := exists_involution_lift_of_odd_center hodd hw ht2
    have h := (isComponentOf_map_iff hψ).2 (hloc K hK K' hK' hKK' t₀ ht₀K ht₀2).2
    rw [map_centralizer_singleton_of_injective hψ] at h
    exact isComponentOf_of_normal_inf hψrange h
  exact odd_projective_linear_commuting_universal_pair_exclusion (Ring.two_ne_zero hk) hn
    ⟨_, _, isQuasisimple_map_of_injective hψ (hπKq K₁ hK₁).1,
      isQuasisimple_map_of_injective hψ (hπKq K₂ hK₂).1,
      by rw [← Subgroup.map_commutator, (hcomm K₁ hK₁ K₂ hK₂ hne).2, Subgroup.map_bot],
      hfour K₁ hK₁, hfour K₂ hK₂, hlocal K₁ hK₁ K₂ hK₂ hne, hlocal K₂ hK₂ K₁ hK₁ (Ne.symm hne)⟩

end CFSG.LocalAnalysis.ComponentInitial
