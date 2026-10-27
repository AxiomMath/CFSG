module

public import CFSG.LocalAnalysis.EvenBN.Sp4.OneAxisData
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCQuotientCoset
public import CFSG.LocalAnalysis.EvenBN.Common.FreeSeries

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

open Subgroup
open CFSG.LocalAnalysis.SymplecticFourStandard CFSG.LocalAnalysis.ComponentInitial
open GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure OneAxisSecondAxis OneAxisWeakClosure
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

namespace OneAxisData

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐔₁" => pull φ (rootU K Axis.one)
local notation "𝐔₂" => pull φ (rootU K Axis.two)
local notation "𝐀₁" => pull φ (rootA K Axis.one)
local notation "𝐀₂" => pull φ (rootA K Axis.two)
local notation "𝐁₁" => (zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G)
local notation "𝐁₂" => (zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
set_option quotPrecheck false in
local notation "𝐒" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G)).subtype : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₂" =>
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄" => (M ⊔ pull φ (antiUnipotent K) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐕" => (M ⊔ pull φ (rootA K Axis.one) ⊔
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom) : Subgroup G)

theorem orbit_eq [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    {x : G | ∃ v ∈ h.V₁, x = v⁻¹ * t * v} =
      {x | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)} := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨a, b, d, hab⟩ := h.exists_hAct (h.V₁_le_T₁ hv)
    exact ⟨a, b + d * a, (h.conj_t_eq hab).2⟩
  · rintro ⟨a, b, rfl⟩
    obtain ⟨m, hm, hab⟩ := h.exists_mem_M₂_hAct a b
    refine ⟨m⁻¹, inv_mem ((le_sup_right : 𝐌₂ ≤ 𝐕) hm), ?_⟩
    rw [inv_inv, (h.conj_t_eq hab).1]

theorem orbit_eq_inter [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    {x : G | ∃ v ∈ h.V₁, x = v⁻¹ * t * v} =
      {x | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁₂} := by
  rw [h.orbit_eq, h.heis.sec.fus]

theorem card_orbit [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    Nat.card {x : G | ∃ v ∈ h.V₁, x = v⁻¹ * t * v} = (2 ^ n) ^ 2 := by
  rw [h.orbit_eq, Hyp.card_pair_set, h.heis.sec.two.card_K]

theorem uElt_eq_mul_mul_mul (a b c : K) :
    uElt a b c 0 = uElt a b 0 0 * (uElt 1 0 0 0 * uElt 0 c 0 0 * uElt 1 c 0 0) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 : uElt (1 : K) 0 0 0 * uElt 0 c 0 0 * uElt 1 c 0 0 = uElt 0 0 c 0 := by
    rw [uElt_mul, uElt_mul]
    congr 1
    all_goals first
      | ring1
      | linear_combination h2
      | linear_combination c * h2
  rw [e1, uElt_mul]
  congr 1 <;> ring

theorem closure_orbit_eq [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    closure {x : G | ∃ v ∈ h.V₁, x = v⁻¹ * t * v} = 𝐁₂ := by
  rw [h.orbit_eq]
  set X := {x : G | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)}
  have hu : ∀ a b : K, ((φ.symm (uElt a b 0 0) : L) : G) ∈ closure X := fun a b => by
    have ht : t ∈ closure X := subset_closure ⟨0, 0, by rw [uElt_zero_eq_one, map_one,
      OneMemClass.coe_one, mul_one]⟩
    have hx : t * ((φ.symm (uElt a b 0 0) : L) : G) ∈ closure X := subset_closure ⟨a, b, rfl⟩
    have := mul_mem (inv_mem ht) hx
    rwa [inv_mul_cancel_left] at this
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨a, b, rfl⟩
    exact mul_mem (mem_sup_left (mem_zpowers t))
      (mem_sup_right (symm_mem_pull.mpr ⟨a, b, 0, rfl⟩))
  · refine sup_le (zpowers_le.mpr (subset_closure ⟨0, 0, by rw [uElt_zero_eq_one, map_one,
      OneMemClass.coe_one, mul_one]⟩)) fun y hy => ?_
    obtain ⟨z, ⟨a, b, c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hy
    rw [uElt_eq_mul_mul_mul, map_mul, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul]
    exact mul_mem (hu a b) (mul_mem (mul_mem (hu 1 0) (hu 0 c)) (hu 1 c))

theorem V₁_inf_centralizer [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    h.V₁ ⊓ centralizer ({t} : Set G) = 𝐏 := by
  have hPV : 𝐏 ≤ 𝐕 := le_sup_right.trans h.E_le_V
  refine le_antisymm (fun x hx => ?_)
    (le_inf hPV fun p hp => h.heis.sec.two.L_le (pull_le φ _ hp))
  obtain ⟨hxV, hxC⟩ := mem_inf.mp hx
  have hxQ := mem_Q_of_comm h.heis (h.V₁_le_T₁ hxV) (mem_centralizer_singleton_iff.mp hxC)
  obtain ⟨p, hp, c, hc, rfl⟩ := h.heis.hyp.setup.mem_Q.mp hxQ
  rw [h.heis.hyp.T_eq] at hc
  have hc' : c = 1 ∨ c = t := by
    obtain ⟨j, rfl⟩ := hc
    exact zpow_eq_one_or_eq h.t_mul_t j
  rcases hc' with rfl | rfl
  · rw [mul_one]
    exact hp
  · exfalso
    apply h.t_not_mem_V₁
    have := mul_mem (inv_mem (hPV hp)) hxV
    rwa [inv_mul_cancel_left] at this

local instance instNormalM₁ [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    (h.M₁.subgroupOf h.V₁).Normal :=
  h.M₁_normal

theorem isElementaryAbelian_quot [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    IsElementaryAbelian 2 (h.V₁ ⧸ h.M₁.subgroupOf h.V₁) := by
  obtain ⟨_, hEA, -⟩ := h.quot_V
  exact hEA

theorem mem_E_of_comm_mem [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) {v : G}
    (hv : v ∈ h.V₁) (hvt : t⁻¹ * v⁻¹ * t * v ∈ h.M₁) : v ∈ 𝐄 := by
  obtain ⟨x, y, d, hxy⟩ := h.exists_hAct (h.V₁_le_T₁ hv)
  have e : t⁻¹ * v⁻¹ * t * v = ((φ.symm (uElt x (y + d * x) 0 0) : L) : G) := by
    rw [show t⁻¹ * v⁻¹ * t * v = t⁻¹ * (v⁻¹ * t * v) by group, (h.conj_t_eq hxy).2,
      inv_mul_cancel_left]
  rw [e] at hvt
  have hZ : ((φ.symm (uElt x (y + d * x) 0 0) : L) : G) ∈ 𝐙 := by
    rw [← h.M₁_inf_B₂]
    exact mem_inf.mpr ⟨hvt, mem_sup_right (symm_mem_pull.mpr ⟨x, y + d * x, 0, rfl⟩)⟩
  obtain ⟨b, c, hbc⟩ := symm_mem_pull.mp hZ
  have hx0 : x = 0 := (uElt_inj hbc).1
  rw [← h.V_inf_R]
  exact mem_inf.mpr ⟨hv, (h.heis.mem_R_iff (h.V₁_le_T₁ hv) hxy).mpr hx0⟩

theorem fixed_eq_range [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    {q | sectionRightConj h.t_mem_normalizer_V₁ h.t_mem_normalizer_M₁ q = q} =
      Set.range fun q : h.V₁ ⧸ h.M₁.subgroupOf h.V₁ =>
        q⁻¹ * sectionRightConj h.t_mem_normalizer_V₁ h.t_mem_normalizer_M₁ q := by
  have hEA := h.isElementaryAbelian_quot
  set α := sectionRightConj h.t_mem_normalizer_V₁ h.t_mem_normalizer_M₁ with hα
  have hPV : 𝐏 ≤ 𝐕 := le_sup_right.trans h.E_le_V
  apply le_antisymm
  · rintro q hq
    obtain ⟨⟨v, hv⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hvt := (sectionRightConj_mk_eq_iff h.t_mem_normalizer_V₁ h.t_mem_normalizer_M₁
      ⟨v, hv⟩).mp hq
    have hvE := h.mem_E_of_comm_mem hv hvt
    rw [← SetLike.mem_coe, ← h.coe_E] at hvE
    obtain ⟨m, hm, p, hp, rfl⟩ := Set.mem_mul.mp hvE
    obtain ⟨z, ⟨a, b, c, d, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hp
    have hsplit : uElt a b c d = uElt 0 0 0 d * uElt a b 0 0 * uElt 0 0 c 0 := by
      rw [uElt_mul, uElt_mul]
      congr 1 <;> ring
    set y₁ : G := ((φ.symm (uElt 0 0 0 d) : L) : G)
    set z : G := ((φ.symm (uElt a b 0 0) : L) : G)
    set y₂ : G := ((φ.symm (uElt 0 0 c 0) : L) : G)
    have hy₁ : y₁ ∈ 𝐌₁ := mem_sup_right (symm_mem_pull.mpr ⟨0, 0, d, rfl⟩)
    have hy₂ : y₂ ∈ 𝐌₁ := mem_sup_left (h.U₂_le (symm_mem_pull.mpr ⟨c, rfl⟩))
    have hzP : z ∈ 𝐏 := symm_mem_pull.mpr ⟨a, b, 0, 0, rfl⟩
    have hz : z ∈ 𝐕 := hPV hzP
    have hp' : ((φ.symm (uElt a b c d) : L) : G) = y₁ * z * y₂ := by
      rw [hsplit, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    have hL : (QuotientGroup.mk (⟨m * ((φ.symm (uElt a b c d) : L) : G), hv⟩ : h.V₁) :
        h.V₁ ⧸ h.M₁.subgroupOf h.V₁) = QuotientGroup.mk ⟨z, hz⟩ := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      have hzS : z⁻¹ ∈ 𝐒 := inv_mem (AxisHyp.P_le_S hzP)
      have hconj := h.conj₁ _ hzS _ (inv_mem (mul_mem (mem_sup_left hm : m ∈ 𝐌₁) hy₁))
      have e : ((⟨m * ((φ.symm (uElt a b c d) : L) : G), hv⟩⁻¹ * ⟨z, hz⟩ : h.V₁) : G) =
          y₂⁻¹ * (z⁻¹ * (m * y₁)⁻¹ * z⁻¹⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hp']
        group
      rw [e]
      exact mul_mem (inv_mem hy₂) hconj
    obtain ⟨m', hm', hab⟩ := h.exists_mem_M₂_hAct a b
    have hm'V : m'⁻¹ ∈ 𝐕 := inv_mem ((le_sup_right : 𝐌₂ ≤ 𝐕) hm')
    have ht' : t⁻¹ * m'⁻¹ * t ∈ 𝐕 := inv_mul_mul_mem_of_mem_normalizer h.t_mem_normalizer_V₁ hm'V
    have hR : (QuotientGroup.mk (⟨m'⁻¹, hm'V⟩ : h.V₁) : h.V₁ ⧸ h.M₁.subgroupOf h.V₁)⁻¹ *
        α (QuotientGroup.mk ⟨m'⁻¹, hm'V⟩) = QuotientGroup.mk ⟨z, hz⟩ := by
      rw [hα, sectionRightConj_mk h.t_mem_normalizer_V₁ h.t_mem_normalizer_M₁ ⟨m'⁻¹, hm'V⟩
        ⟨t⁻¹ * m'⁻¹ * t, ht'⟩ rfl, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      have e := (h.conj_t_eq hab).1
      have htt : t⁻¹ = t := h.heis.sec.two.t_inv
      change m'⁻¹⁻¹ * (t⁻¹ * m'⁻¹ * t) = z
      rw [inv_inv, htt, show m' * (t * m'⁻¹ * t) = m' * t * m'⁻¹ * t by group, e, mul_assoc,
        ← h.comm_L (φ.symm _).2, ← mul_assoc, h.t_mul_t, one_mul]
    exact ⟨QuotientGroup.mk ⟨m'⁻¹, hm'V⟩, hR.trans hL.symm⟩
  · rintro _ ⟨q, rfl⟩
    change α (q⁻¹ * α q) = q⁻¹ * α q
    have hinv : ∀ r : h.V₁ ⧸ h.M₁.subgroupOf h.V₁, r⁻¹ = r := fun r =>
      inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_isElementaryAbelian_two r)
    rw [map_mul, map_inv, Common.sectionRightConj_sectionRightConj _ _ h.t_mul_t, hinv, hinv,
      mul_comm' (α q) q]

theorem involution_coset_eq [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    {x : G | (∃ v ∈ h.V₁, x = t * v) ∧ orderOf x = 2} =
      {x | ∃ v ∈ h.V₁, ∃ a ∈ 𝐀₁, x = v⁻¹ * (t * a) * v} := by
  have hEA := h.isElementaryAbelian_quot
  have hM₁ : IsElementaryAbelian 2 h.M₁ := h.elemAb₁
  have hfix := h.fixed_eq_range
  rw [← coe_closure_range_inv_mul_apply] at hfix
  have hres := (elementary_quotient_involution_coset_conjugacy (V := h.V₁) (E := h.M₁)
    le_sup_left h.heis.hyp.setup.order_t h.t_mem_normalizer_V₁ h.t_mem_normalizer_M₁
    h.t_not_mem_V₁ hfix).1
  rw [hres, h.M₁_inf_centralizer]

theorem class_slice [Finite G] [Finite K]
    (h : OneAxisData L K n φ TG t M) :
    {x : G | ∃ g : G, x = g⁻¹ * t * g} ∩ (h.T₁ : Set G) =
      {x | ∃ v ∈ h.V₁, x = v⁻¹ * t * v} := by
  ext x
  constructor
  · rintro ⟨⟨g, rfl⟩, hgT⟩
    have hgT' : g⁻¹ * t * g ∈ zpowers t ⊔ h.V₁ := by
      rw [sup_comm, ← h.T₁_eq.1]
      exact hgT
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
      (zpowers_le.mpr h.t_mem_normalizer_V₁)] at hgT'
    obtain ⟨c, hc, v, hv, hcv⟩ := Set.mem_mul.mp hgT'
    have hc' : c = 1 ∨ c = t := by
      obtain ⟨j, rfl⟩ := hc
      exact zpow_eq_one_or_eq h.t_mul_t j
    rcases hc' with rfl | hct
    · exfalso
      rw [one_mul] at hcv
      refine OneAxisInvolutionExclusion.conj_not_mem_V h.toAxisHyp h.elemAb₁ g ?_
      rw [← hcv]
      exact hv
    · rw [hct] at hcv
      have hord : orderOf (g⁻¹ * t * g) = 2 := by
        have e := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
        rw [MulAut.conj_apply, inv_inv] at e
        rw [e, h.heis.hyp.setup.order_t]
      have hmem : g⁻¹ * t * g ∈ {x : G | (∃ v ∈ h.V₁, x = t * v) ∧ orderOf x = 2} :=
        ⟨⟨v, hv, hcv.symm⟩, hord⟩
      rw [h.involution_coset_eq] at hmem
      obtain ⟨w, hw, a, ha, hwa⟩ := hmem
      have hta : t * a ∈ {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁₁} := by
        refine ⟨⟨g * w⁻¹, ?_⟩, mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right ha)⟩
        have e : t * a = w * (g⁻¹ * t * g) * w⁻¹ := by rw [hwa]; group
        rw [e]
        group
      rw [h.heis.hyp.fus_one] at hta
      obtain ⟨u, hu, htu⟩ := hta
      obtain ⟨m, hm, hmu⟩ := h.exists_mem_M₁_conj_eq hu
      refine ⟨m * w, mul_mem ((le_sup_left : 𝐌₁ ≤ 𝐕) hm) hw, ?_⟩
      rw [hwa, htu, ← hmu]
      group
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, mul_mem (mul_mem (inv_mem (h.V₁_le_T₁ hv)) h.t_mem_T₁) (h.V₁_le_T₁ hv)⟩

end OneAxisData

open OneAxisData

theorem one_axis_class_slice {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {φ : L ≃* antiSp K}
    {TG : Subgroup G} {t : G} {M : Subgroup G} (h : OneAxisData L K n φ TG t M) :
    {x : G | ∃ g : G, x = g⁻¹ * t * g} ∩ (h.T₁ : Set G) =
        {x | ∃ v ∈ h.V₁, x = v⁻¹ * t * v} ∧
      (h.T₁ = h.V₁ ⊔ zpowers t ∧ h.V₁ ⊓ zpowers t = ⊥) ∧
      {x : G | ∃ v ∈ h.V₁, x = v⁻¹ * t * v} =
        {x | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ zpowers t ⊔ pull φ (rootA K Axis.two)} ∧
      {x : G | ∃ v ∈ h.V₁, x = v⁻¹ * t * v} =
        {x | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)} ∧
      Nat.card {x : G | ∃ v ∈ h.V₁, x = v⁻¹ * t * v} = (2 ^ n) ^ 2 ∧
      closure {x : G | ∃ v ∈ h.V₁, x = v⁻¹ * t * v} = zpowers t ⊔ pull φ (rootA K Axis.two) ∧
      h.V₁ ⊓ centralizer ({t} : Set G) = pull φ (antiUnipotent K) ∧
      {x : G | (∃ v ∈ h.V₁, x = t * v) ∧ orderOf x = 2} =
        {x | ∃ v ∈ h.V₁, ∃ a ∈ pull φ (rootA K Axis.one), x = v⁻¹ * (t * a) * v} :=
  ⟨h.class_slice, h.T₁_eq, h.orbit_eq_inter, h.orbit_eq, h.card_orbit, h.closure_orbit_eq,
    h.V₁_inf_centralizer, h.involution_coset_eq⟩

end CFSG.LocalAnalysis.EvenBN.Sp4
