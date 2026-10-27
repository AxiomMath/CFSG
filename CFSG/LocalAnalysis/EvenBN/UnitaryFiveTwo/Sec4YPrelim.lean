module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4C0

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement

@[expose] def Data.U {G : Type} [Group G] (d : Data G) : Subgroup G :=
  d.C₀ ⊓ centralizer ({d.e₂} : Set G)

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem e₂_comm_t (h : d.Hyp) : d.e₂ * d.t = d.t * d.e₂ :=
  comm_of_mem_centralizer h.t_mem (d.ι_mem _)

omit [Finite G] in
theorem e₂_comm_F {f : G} (hf : f ∈ d.F) : d.e₂ * f = f * d.e₂ := by
  obtain ⟨φ, hφ, rfl⟩ := hf
  rw [Data.e₂, ← map_mul, ← map_mul, e₂SU_comm_Fsub hφ]

omit [Finite G] in
theorem e₂_pow_three : d.e₂ ^ 3 = 1 := by
  rw [Data.e₂, ← map_pow, ← orderOf_e₂SU, pow_orderOf_eq_one, map_one]

theorem e₂_mem_normalizer
    (h : d.Hyp) :
    d.e₂ ∈ normalizer ((d.withT d.F : Subgroup G) : Set G) := by
  rw [h.normalizer_withT_F_eq]
  exact h.ι_mem_normalizer fun a ha =>
    DiagSub_conj_mem_A₂sub (Esub_le_DiagSub (mem_sup_right (mem_zpowers _))) ha

theorem e₂_conj_mem_C₀
    (h : d.Hyp) {x : G} (hx : x ∈ d.C₀) :
    d.e₂ * x * d.e₂⁻¹ ∈ d.C₀ :=
  conj_mem_oTwo (X := normalizer ((d.withT d.F : Subgroup G) : Set G)) h.e₂_mem_normalizer hx

theorem exists_U_crossed_eq
    (h : d.Hyp) {a : G} (ha : a ∈ d.F) :
    ∃ x ∈ d.U, x⁻¹ * d.t * x * d.t = a := by
  obtain ⟨x₀, hx₀, e₀⟩ := h.exists_crossed_eq ha
  rw [← h.C₀_eq_X₀] at hx₀
  set T : Set G := {x | x ∈ d.C₀ ∧ x⁻¹ * d.t * x * d.t = a} with hT
  have hTe : ∀ x ∈ T, d.e₂ * x * d.e₂⁻¹ ∈ T := by
    rintro x ⟨hx, hxa⟩
    refine ⟨h.e₂_conj_mem_C₀ hx, ?_⟩
    rw [crossed_conj h.e₂_comm_t, hxa, mul_inv_eq_iff_eq_mul, e₂_comm_F ha]
  have hTeq : T = (fun k => k * x₀) '' ((d.withT d.A₂ : Subgroup G) : Set G) := by
    ext x
    constructor
    · rintro ⟨hx, hxa⟩
      refine ⟨x * x₀⁻¹, ?_, by group⟩
      rw [← h.H_inf_C₀]
      refine Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mul_mem hx (inv_mem hx₀)⟩
      have e : x⁻¹ * d.t * x = x₀⁻¹ * d.t * x₀ := mul_right_cancel (hxa.trans e₀.symm)
      calc x * x₀⁻¹ * d.t = x * (x₀⁻¹ * d.t * x₀) * x₀⁻¹ := by group
        _ = x * (x⁻¹ * d.t * x) * x₀⁻¹ := by rw [e]
        _ = d.t * (x * x₀⁻¹) := by group
    · rintro ⟨k, hk, rfl⟩
      rw [← h.H_inf_C₀] at hk
      obtain ⟨hkH, hkC⟩ := Subgroup.mem_inf.1 hk
      refine ⟨mul_mem hkC hx₀, ?_⟩
      have hkt : k⁻¹ * d.t * k = d.t := by
        rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hkH]
        group
      calc (k * x₀)⁻¹ * d.t * (k * x₀) * d.t = x₀⁻¹ * (k⁻¹ * d.t * k) * x₀ * d.t := by group
        _ = a := by rw [hkt, e₀]
  have hcard : T.ncard = 2 ^ 9 := by
    rw [hTeq, Set.ncard_image_of_injective _ (mul_left_injective x₀), ← Nat.card_coe_set_eq]
    exact h.card_withT_A₂_eq
  obtain ⟨x, ⟨hx, hxa⟩, hfix⟩ := exists_conj_fixed e₂_pow_three hTe (by rw [hcard]; norm_num)
  refine ⟨x, Subgroup.mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 ?_⟩, hxa⟩
  calc x * d.e₂ = d.e₂ * x * d.e₂⁻¹ * d.e₂ := by rw [hfix]
    _ = d.e₂ * x := by group

omit [Finite G] in
theorem U_le_C₀ : d.U ≤ d.C₀ := inf_le_left

theorem U_comm_F
    (h : d.Hyp) {x f : G} (hx : x ∈ d.U) (hf : f ∈ d.F) :
    x * f = f * x :=
  h.comm_F_of_mem_X₀ (h.C₀_eq_X₀ ▸ U_le_C₀ hx) hf

theorem U_crossed_mem_F
    (h : d.Hyp) {x : G} (hx : x ∈ d.U) :
    x⁻¹ * d.t * x * d.t ∈ d.F :=
  h.crossed_mem_F (h.C₀_eq_X₀ ▸ U_le_C₀ hx)

theorem U_inf_H
    (h : d.Hyp) : d.U ⊓ d.H = d.withT d.F := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU, hxH⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxC, hxe⟩ := Subgroup.mem_inf.1 hxU
    have hxP : x ∈ d.withT d.A₂ := by
      rw [← h.H_inf_C₀]
      exact Subgroup.mem_inf.2 ⟨hxH, hxC⟩
    obtain ⟨_, ⟨α, hα, rfl⟩, c, hc, rfl⟩ := h.exists_eq_mul_of_mem_withT_A₂ hxP
    have hce : c * d.ι e₂SU = d.ι e₂SU * c := ((h.comm_zpowers_t hc).1 _ (d.ι_mem _)).symm
    have he : d.ι α * c * d.ι e₂SU = d.ι e₂SU * (d.ι α * c) := mem_centralizer_singleton_iff.1 hxe
    have hαe : e₂SU * α = α * e₂SU := d.ι_injective (by
      rw [map_mul, map_mul]
      calc d.ι e₂SU * d.ι α = d.ι e₂SU * (d.ι α * c) * c⁻¹ := by group
        _ = d.ι α * c * d.ι e₂SU * c⁻¹ := by rw [← he]
        _ = d.ι α * (c * d.ι e₂SU) * c⁻¹ := by group
        _ = d.ι α * (d.ι e₂SU * c) * c⁻¹ := by rw [hce]
        _ = d.ι α * d.ι e₂SU := by group)
    exact mul_mem (mem_sup_left (d.ι_mem_pull_iff.2 (mem_Fsub_of_comm_e₂ hα hαe)))
      (mem_sup_right hc)
  · have hFP : d.withT d.F ≤ d.withT d.A₂ := sup_le_sup_right d.F_le_A₂ _
    have hC : d.withT d.F ≤ d.C₀ := hFP.trans (h.C₀_eq_X₀ ▸ h.withT_A₂_le_X₀)
    have hH : d.withT d.F ≤ d.H := h.withT_F_le_H
    refine le_inf (le_inf hC ?_) hH
    refine sup_le (fun f hf => mem_centralizer_singleton_iff.2 (e₂_comm_F hf).symm) ?_
    exact zpowers_le.2 (mem_centralizer_singleton_iff.2 h.e₂_comm_t.symm)

theorem t_mem_U
    (h : d.Hyp) : d.t ∈ d.U := by
  have : d.t ∈ d.U ⊓ d.H := by
    rw [h.U_inf_H]
    exact mem_sup_right (mem_zpowers _)
  exact (Subgroup.mem_inf.1 this).1

theorem F_le_U
    (h : d.Hyp) : d.F ≤ d.U := fun f hf => by
  have : f ∈ d.U ⊓ d.H := by
    rw [h.U_inf_H]
    exact mem_sup_left hf
  exact (Subgroup.mem_inf.1 this).1

theorem card_U
    (h : d.Hyp) : Nat.card d.U = 2 ^ 9 := by
  have := card_eq_of_crossed_onto h.t_mul_t
    (fun x hx => mem_centralizer_iff.2 fun f hf => (h.U_comm_F hx hf).symm)
    (fun _ hy => h.U_crossed_mem_F hy) fun _ hb => h.exists_U_crossed_eq hb
  rw [show (d.U ⊓ centralizer ({d.t} : Set G) : Subgroup G) = d.withT d.F from h.U_inf_H,
    h.card_withT_F, d.card_F] at this
  rw [this]
  norm_num

theorem U_inf_A₂
    (h : d.Hyp) : d.U ⊓ d.A₂ = d.F := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.F_le_U d.F_le_A₂)
  obtain ⟨hxU, hxA⟩ := Subgroup.mem_inf.1 hx
  have hxH : x ∈ d.H := h.L_le_H (d.pull_le_L _ hxA)
  have hxZ : x ∈ d.withT d.F := by
    rw [← h.U_inf_H]
    exact Subgroup.mem_inf.2 ⟨hxU, hxH⟩
  exact h.mem_F_of_mem_withT_F_of_mem_L hxZ (d.pull_le_L _ hxA)

theorem C₀_eq_sup
    (h : d.Hyp) : d.C₀ = d.A₂ ⊔ d.U := by
  refine le_antisymm (fun c hc => ?_) (sup_le ?_ U_le_C₀)
  · obtain ⟨u, hu, eu⟩ := h.exists_U_crossed_eq (h.crossed_mem_F (h.C₀_eq_X₀ ▸ hc))
    have hcu : c * u⁻¹ ∈ d.withT d.A₂ := by
      rw [← h.H_inf_C₀]
      refine Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_,
        mul_mem hc (inv_mem (U_le_C₀ hu))⟩
      have e : c⁻¹ * d.t * c = u⁻¹ * d.t * u := mul_right_cancel eu.symm
      calc c * u⁻¹ * d.t = c * (u⁻¹ * d.t * u) * u⁻¹ := by group
        _ = c * (c⁻¹ * d.t * c) * u⁻¹ := by rw [e]
        _ = d.t * (c * u⁻¹) := by group
    obtain ⟨a, ha, k, hk, hak⟩ := h.exists_eq_mul_of_mem_withT_A₂ hcu
    have hkU : k ∈ d.U := zpowers_le.2 h.t_mem_U hk
    have e : c = a * (k * u) := by
      rw [← mul_assoc, ← hak]
      group
    rw [e]
    exact mul_mem (mem_sup_left ha) (mem_sup_right (mul_mem hkU hu))
  · have hP : d.withT d.A₂ ≤ d.C₀ := by
      rw [h.C₀_eq_X₀]
      exact h.withT_A₂_le_X₀
    exact le_sup_left.trans hP

theorem U_sq
    (h : d.Hyp) {x : G} (hx : x ∈ d.U) : x * x ∈ d.F := by
  have hxC : x ∈ X₀ d := h.C₀_eq_X₀ ▸ U_le_C₀ hx
  have hcr : (x * x)⁻¹ * d.t * (x * x) * d.t = 1 := by
    rw [crossed_mul h.t_mul_t ((h.U_comm_F hx (h.U_crossed_mem_F hx)).symm),
      h.F_sq (h.U_crossed_mem_F hx)]
  have hxx : x * x ∈ d.withT d.F := by
    rw [← h.U_inf_H]
    exact Subgroup.mem_inf.2 ⟨mul_mem hx hx, mem_centralizer_singleton_iff.2
      ((crossed_eq_one_iff h.t_mul_t).1 hcr)⟩
  obtain ⟨f, hf, k, hk⟩ := h.exists_eq_mul_of_mem_withT_F hxx
  have hk' : d.t ^ k = d.t ^ (k % 2) := by
    rw [← zpow_mod_orderOf, h.t_two]
    norm_cast
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [hk, hk', h0, zpow_zero, mul_one]
    exact hf
  · exfalso
    rw [hk', h1, zpow_one] at hk
    obtain ⟨u, hu, eu⟩ := h.exists_U_crossed_eq hf
    have e1 : x * x = u⁻¹ * d.t * u := by
      rw [hk, ← eu, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
    obtain ⟨y, hy⟩ : ∃ y, y = u * x * u⁻¹ := ⟨_, rfl⟩
    have hyU : y ∈ d.U := hy ▸ mul_mem (mul_mem hu hx) (inv_mem hu)
    have hyy : y * y = d.t := by
      rw [hy, show u * x * u⁻¹ * (u * x * u⁻¹) = u * (x * x) * u⁻¹ by group, e1]
      group
    have hyt : y * d.t = d.t * y := by rw [← hyy, ← mul_assoc]
    have hyZ : y ∈ d.withT d.F := by
      rw [← h.U_inf_H]
      exact Subgroup.mem_inf.2 ⟨hyU, mem_centralizer_singleton_iff.2 hyt⟩
    have h1 : y * y = 1 := by
      obtain ⟨g, hg, j, rfl⟩ := h.exists_eq_mul_of_mem_withT_F hyZ
      have hgt : d.t ^ j * g = g * d.t ^ j := (Commute.zpow_right (h.t_comm_F hg) j).eq.symm
      calc g * d.t ^ j * (g * d.t ^ j) = g * g * (d.t ^ j * d.t ^ j) := by
            rw [show g * d.t ^ j * (g * d.t ^ j) = g * (d.t ^ j * g) * d.t ^ j by group, hgt]
            group
        _ = 1 := by
            rw [h.F_sq hg, one_mul, ← zpow_add, ← two_mul, zpow_mul, zpow_two, h.t_mul_t,
              one_zpow]
    exact h.t_ne_one (hyy.symm.trans h1)

theorem commutator_U_mem_F
    (h : d.Hyp) {x y : G} (hx : x ∈ d.U) (hy : y ∈ d.U) :
    ⁅x, y⁆ ∈ d.F := by
  have hxx := h.U_sq hx
  have hyy := h.U_sq hy
  have hxy := h.U_sq (mul_mem hx hy)
  have hxi : x⁻¹ = (x * x)⁻¹ * x := by group
  have hyi : y⁻¹ = (y * y)⁻¹ * y := by group
  have ca : (x * x)⁻¹ * x = x * (x * x)⁻¹ := (h.U_comm_F hx (inv_mem hxx)).symm
  have cay : (x * x)⁻¹ * y = y * (x * x)⁻¹ := (h.U_comm_F hy (inv_mem hxx)).symm
  have cby : (y * y)⁻¹ * y = y * (y * y)⁻¹ := (h.U_comm_F hy (inv_mem hyy)).symm
  rw [commutatorElement_def, hxi, hyi, ca]
  have e : x * y * (x * (x * x)⁻¹) * ((y * y)⁻¹ * y) =
      (x * y * (x * y)) * ((x * x)⁻¹ * (y * y)⁻¹) := by
    calc _ = x * y * x * ((x * x)⁻¹ * ((y * y)⁻¹ * y)) := by group
      _ = x * y * x * ((x * x)⁻¹ * (y * (y * y)⁻¹)) := by rw [cby]
      _ = x * y * x * (((x * x)⁻¹ * y) * (y * y)⁻¹) := by group
      _ = x * y * x * ((y * (x * x)⁻¹) * (y * y)⁻¹) := by rw [cay]
      _ = _ := by group
  rw [e]
  exact mul_mem hxy (mul_mem (inv_mem hxx) (inv_mem hyy))

theorem conj_mul_inv_mem_F_of_C₀
    (h : d.Hyp) {c a : G}
    (hc : c ∈ d.C₀) (ha : a ∈ d.A₂) : c * a * c⁻¹ * a⁻¹ ∈ d.F := by
  have hcX : c ∈ X₀ d := h.C₀_eq_X₀ ▸ hc
  have h1 := h.conj_mul_inv_mem_of_mem_X₀ hcX (mem_sup_left ha : a ∈ d.withT d.A₂)
  have hcN : c ∈ normalizer (d.A₂ : Set G) :=
    h.normalizer_withT_F_le ((h.normalizer_withT_F_eq).symm ▸ X₀_le hcX)
  have h2 : c * a * c⁻¹ * a⁻¹ ∈ d.A₂ := mul_mem ((mem_normalizer_iff.1 hcN a).1 ha) (inv_mem ha)
  exact h.mem_F_of_mem_withT_F_of_mem_L h1 (d.pull_le_L _ h2)

theorem sec4_6_U
    (h : d.Hyp) :
    d.C₀ = d.A₂ ⊔ d.U ∧ d.U ⊓ d.A₂ = d.F ∧ d.U ⊓ d.H = d.withT d.F ∧ Nat.card d.U = 2 ^ 9 ∧
      (∀ a ∈ d.F, ∃ x ∈ d.U, x⁻¹ * d.t * x = a * d.t) ∧ (∀ x ∈ d.U, x * x ∈ d.F) ∧
      (∀ x ∈ d.U, ∀ y ∈ d.U, ⁅x, y⁆ ∈ d.F) ∧ ∀ x ∈ d.U, ∀ f ∈ d.F, x * f = f * x := by
  refine ⟨h.C₀_eq_sup, h.U_inf_A₂, h.U_inf_H, h.card_U, fun a ha => ?_,
    fun x hx => h.U_sq hx, fun x hx y hy => h.commutator_U_mem_F hx hy,
    fun x hx f hf => h.U_comm_F hx hf⟩
  obtain ⟨x, hx, e⟩ := h.exists_U_crossed_eq ha
  exact ⟨x, hx, by rw [← e, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]⟩

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
