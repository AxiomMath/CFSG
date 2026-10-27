module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbSylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbGens
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbType

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.Asc75Lemma31
open scoped commutatorElement

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

omit [Finite G] h hP hPC in
theorem conj_commutatorElement (x u v : G) : x * ⁅u, v⁆ * x⁻¹ = ⁅x * u * x⁻¹, x * v * x⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

omit hP hPC in
theorem commP_V_V {v v' : G} (hv : v ∈ R ⊔ T) (hv' : v' ∈ R ⊔ T) : ⁅v, v'⁆ = 1 := by
  rw [commutatorElement_def, h.comm hv hv']
  group

omit [Finite G] h hPC in
theorem commP_V₀_left {w u : G} (hw : w ∈ V₀) (hu : u ∈ P) : ⁅w, u⁆ = 1 := by
  rw [commutatorElement_def, ← P_comm_V₀ hP hw hu]
  group

omit [Finite G] h hPC in
theorem commP_V₀_right {u w : G} (hu : u ∈ P) (hw : w ∈ V₀) : ⁅u, w⁆ = 1 := by
  rw [commutatorElement_def, P_comm_V₀ hP hw hu]
  group

theorem mem_V_of_commP_eq_one {u r : G} (hu : u ∈ P) (hr : r ∈ R) (hr1 : r ≠ 1)
    (h1 : ⁅u, r⁆ = 1) : u ∈ R ⊔ T := by
  by_contra huV
  have := h.mem_V₀_of_commP_eq_one hP hPC hu huV (mem_sup_left hr) h1
  have h2 : r ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr, this⟩
  rw [h.inf_R_V₀, mem_bot] at h2
  exact hr1 h2

theorem inv_mul_mem_V_of_commP_eq {u u' r : G} (hu : u ∈ P) (hu' : u' ∈ P) (hr : r ∈ R)
    (hr1 : r ≠ 1) (he : ⁅u, r⁆ = ⁅u', r⁆) : u⁻¹ * u' ∈ R ⊔ T := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hrP : r ∈ P := hVP (mem_sup_left hr)
  apply h.mem_V_of_commP_eq_one hP hPC (mul_mem (inv_mem hu) hu') hr hr1
  have hinv : ⁅u⁻¹, r⁆ = ⁅u, r⁆⁻¹ := by
    have h1 := h.commP_mul_left hP hPC (inv_mem hu) hu hrP
    rw [inv_mul_cancel, commutatorElement_one_left] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  rw [h.commP_mul_left hP hPC (inv_mem hu) hu' hrP, hinv, he, inv_mul_cancel]

theorem commP_swap {u v : G} (hu : u ∈ P) (hv : v ∈ P) : ⁅v, u⁆ = ⁅u, v⁆ := by
  rw [← commutatorElement_inv]
  exact inv_eq_of_mul_eq_one_right (h.mul_self (h.V₀_le (h.commP_mem hP hPC hu hv)))

theorem commP_mul_self {u v : G} (hu : u ∈ P) (hv : v ∈ P) : ⁅u, v⁆ * ⁅u, v⁆ = 1 :=
  h.mul_self (h.V₀_le (h.commP_mem hP hPC hu hv))

theorem mul_self_mul_P {u v : G} (hu : u ∈ P) (hv : v ∈ P) :
    u * v * (u * v) = u * u * (v * v) * ⁅u, v⁆ := by
  have hc := h.commP_mem hP hPC hv hu
  have hcvv : ⁅v, u⁆ * (u * (v * v)) = u * (v * v) * ⁅v, u⁆ :=
    (P_comm_V₀ hP hc (mul_mem hu (mul_mem hv hv))).symm
  have hvu : v * u = ⁅v, u⁆ * u * v := by simp only [commutatorElement_def]; group
  calc u * v * (u * v) = u * (v * u) * v := by group
    _ = u * (⁅v, u⁆ * u * v) * v := by rw [hvu]
    _ = u * (⁅v, u⁆ * (u * (v * v))) := by group
    _ = u * (u * (v * v) * ⁅v, u⁆) := by rw [hcvv]
    _ = u * u * (v * v) * ⁅u, v⁆ := by rw [h.commP_swap hP hPC hu hv]; group

variable {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

omit [Finite G] h hP hPC in
theorem outer_conj_r : x * r₁ * x⁻¹ = r₁ := by
  rw [hx.r_comm]; group

omit [Finite G] h hP hPC in
theorem outer_conj_z : x * z * x⁻¹ = z := by
  rw [hx.z_comm]; group

theorem exists_invol_fixed :
    ∃ c₁ ∈ P, c₁ ∉ R ⊔ T ∧ c₁ * c₁ = 1 ∧ c₁⁻¹ * (x * c₁ * x⁻¹) ∈ V₀ := by
  obtain ⟨p, hp, hpx⟩ := hx.move
  have hxp : x * p * x⁻¹ ∈ P := (mem_normalizer_iff.mp hx.normP p).mp hp
  set y := p * (x * p * x⁻¹) with hy
  have hyP : y ∈ P := mul_mem hp hxp
  have hpp := h.P_sq_mem_V hP hPC hp
  have hyV : y ∉ R ⊔ T := by
    intro hyV
    apply hpx
    have e : p⁻¹ * (x * p * x⁻¹) = (p * p)⁻¹ * y := by rw [hy]; group
    rw [e]
    exact mul_mem (inv_mem hpp) hyV
  have hxi : x⁻¹ = x := outer_inv hx
  have hyy : y⁻¹ * (x * y * x⁻¹) ∈ R ⊔ T := by
    have e : y⁻¹ * (x * y * x⁻¹) = (x * p * x⁻¹)⁻¹ * p⁻¹ * (x * p * x⁻¹)⁻¹⁻¹ * p⁻¹⁻¹ := by
      rw [hy]
      calc (p * (x * p * x⁻¹))⁻¹ * (x * (p * (x * p * x⁻¹)) * x⁻¹) =
          (x * p * x⁻¹)⁻¹ * p⁻¹ * (x * p * x⁻¹) * (x * x * p * x⁻¹ * x⁻¹) := by group
        _ = (x * p * x⁻¹)⁻¹ * p⁻¹ * (x * p * x⁻¹)⁻¹⁻¹ * p⁻¹⁻¹ := by
            rw [hx.sq, show (1 : G) * p * x⁻¹ * x⁻¹ = p by rw [hxi, one_mul, mul_assoc, hx.sq,
              mul_one]]
            group
    rw [e]
    exact h.V₀_le (h.P_comm_mem_V₀_of_sq hP hPC (inv_mem hxp) (inv_mem hp))
  obtain ⟨v, hv, hyv⟩ := h.P_exists_invol hP hPC hyP hyV
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hxv : x * v * x⁻¹ ∈ R ⊔ T := (mem_normalizer_iff.mp hx.normV v).mp hv
  refine ⟨y * v, mul_mem hyP (hVP hv), fun he => hyV ?_, hyv, ?_⟩
  · have := mul_mem he (inv_mem hv)
    rwa [mul_inv_cancel_right] at this
  · have hc1V : y * v ∉ R ⊔ T := fun he => hyV (by
      have := mul_mem he (inv_mem hv)
      rwa [mul_inv_cancel_right] at this)
    have hmem : (y * v)⁻¹ * (x * (y * v) * x⁻¹) ∈ R ⊔ T := by
      have e : (y * v)⁻¹ * (x * (y * v) * x⁻¹) = v⁻¹ * (y⁻¹ * (x * y * x⁻¹)) * (x * v * x⁻¹) := by
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hv) hyy) hxv
    refine h.P_invol_coset hP hPC (mul_mem hyP (hVP hv)) hc1V hyv hmem ?_
    have e : y * v * ((y * v)⁻¹ * (x * (y * v) * x⁻¹)) *
        (y * v * ((y * v)⁻¹ * (x * (y * v) * x⁻¹))) = x * (y * v * (y * v)) * x⁻¹ := by group
    rw [e, hyv]
    group

theorem commP_eq_z {c₁ : G} (hc₁ : c₁ ∈ P) (hc₁V : c₁ ∉ R ⊔ T)
    (hc₁x : c₁⁻¹ * (x * c₁ * x⁻¹) ∈ V₀) : ⁅c₁, r₁⁆ = z := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hr₁P : r₁ ∈ P := hVP (mem_sup_left hx.r_mem)
  set u := c₁⁻¹ * (x * c₁ * x⁻¹) with hu
  have hs := h.commP_mem hP hPC hc₁ hr₁P
  have hfix : x * ⁅c₁, r₁⁆ * x⁻¹ = ⁅c₁, r₁⁆ := by
    rw [conj_commutatorElement, outer_conj_r hx,
      show x * c₁ * x⁻¹ = c₁ * u by rw [hu]; group,
      h.commP_mul_left hP hPC hc₁ (hVP (h.V₀_le hc₁x)) hr₁P,
      commP_V₀_left hP hc₁x hr₁P, mul_one]
  have hs1 : ⁅c₁, r₁⁆ ≠ 1 := fun he =>
    hc₁V (h.mem_V_of_commP_eq_one hP hPC hc₁ hx.r_mem hx.r_ne he)
  rcases hx.fix_V₀ _ hs (by
    calc x * ⁅c₁, r₁⁆ = x * ⁅c₁, r₁⁆ * x⁻¹ * x := by group
      _ = ⁅c₁, r₁⁆ * x := by rw [hfix]) with h1 | h1
  · exact absurd h1 hs1
  · exact h1

theorem outer_conj_mem_coset {c₁ c : G} (hc₁ : c₁ ∈ P) (hc₁V : c₁ ∉ R ⊔ T)
    (hc₁x : c₁⁻¹ * (x * c₁ * x⁻¹) ∈ R ⊔ T) (hc : c ∈ P) (hcV : c ∉ R ⊔ T)
    (hc₁c : c₁⁻¹ * c ∉ R ⊔ T) : (c₁ * c)⁻¹ * (x * c * x⁻¹) ∈ R ⊔ T := by
  have hxi : x⁻¹ = x := outer_inv hx
  have hxV : ∀ {v : G}, v ∈ R ⊔ T → x * v * x⁻¹ ∈ R ⊔ T := fun hv =>
    (mem_normalizer_iff.mp hx.normV _).mp hv
  have hxP : x * c * x⁻¹ ∈ P := (mem_normalizer_iff.mp hx.normP c).mp hc
  have hVN : ∀ {u v : G}, u ∈ P → v ∈ R ⊔ T → u * v * u⁻¹ ∈ R ⊔ T := fun hu hv =>
    (mem_normalizer_iff.mp (hP.le hu).1 _).mp hv
  rcases h.mem_cosets hP hPC hc₁ hc₁V hc hcV hc₁c hxP with h1 | h1 | h1 | h1
  · exfalso
    apply hcV
    have := hxV h1
    rwa [show x * (x * c * x⁻¹) * x⁻¹ = (x * x) * c * (x * x)⁻¹ by group, hx.sq, one_mul,
      inv_one, mul_one] at this
  · exfalso
    apply hc₁c
    have e : c₁⁻¹ * c = (c₁⁻¹ * (x * c₁ * x⁻¹)) * (x * (c₁⁻¹ * (x * c * x⁻¹)) * x⁻¹) := by
      rw [show x * (c₁⁻¹ * (x * c * x⁻¹)) * x⁻¹ = x * c₁⁻¹ * x⁻¹ * ((x * x) * c * (x * x)⁻¹)
        by group, hx.sq, one_mul, inv_one, mul_one]
      group
    rw [e]
    exact mul_mem hc₁x (hxV h1)
  · exfalso
    obtain ⟨p, hp, hpx⟩ := hx.move
    apply hpx
    rcases h.mem_cosets hP hPC hc₁ hc₁V hc hcV hc₁c hp with h2 | h2 | h2 | h2
    · exact mul_mem (inv_mem h2) (hxV h2)
    · have e : p⁻¹ * (x * p * x⁻¹) = (c₁⁻¹ * p)⁻¹ * (c₁⁻¹ * (x * c₁ * x⁻¹)) *
          (x * (c₁⁻¹ * p) * x⁻¹) := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem h2) hc₁x) (hxV h2)
    · have e : p⁻¹ * (x * p * x⁻¹) = (c⁻¹ * p)⁻¹ * (c⁻¹ * (x * c * x⁻¹)) *
          (x * (c⁻¹ * p) * x⁻¹) := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem h2) h1) (hxV h2)
    · have e : p⁻¹ * (x * p * x⁻¹) = ((c₁ * c)⁻¹ * p)⁻¹ *
          (c⁻¹ * ((c₁⁻¹ * (x * c₁ * x⁻¹)) * c) * (c⁻¹ * (x * c * x⁻¹))) *
            (x * ((c₁ * c)⁻¹ * p) * x⁻¹) := by group
      rw [e]
      refine mul_mem (mul_mem (inv_mem h2) (mul_mem ?_ h1)) (hxV h2)
      have := hVN (inv_mem hc) hc₁x
      rw [inv_inv] at this
      simpa only [mul_assoc] using this
  · exact h1

omit hP hPC in
theorem outer_conj_R_of_ne {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) (hrr₁ : r ≠ r₁) :
    x * r * x⁻¹ = r * r₁ := by
  have hR2 : ∀ y ∈ R, y * y = 1 := fun y hy => h.mul_self (mem_sup_left hy)
  have hxr : x * r * x⁻¹ ∈ R := (mem_normalizer_iff.mp hx.normR r).mp hr
  have hxr1 : x * r * x⁻¹ ≠ 1 := fun h1 => hr1 (by
    calc r = x⁻¹ * (x * r * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group)
  have hxrr : x * r * x⁻¹ ≠ r := fun h1 => by
    rcases hx.fix_R r hr (by
      calc x * r = x * r * x⁻¹ * x := by group
        _ = r * x := by rw [h1]) with h2 | h2
    · exact hr1 h2
    · exact hrr₁ h2
  have hxrr₁ : x * r * x⁻¹ ≠ r₁ := fun h1 => hrr₁ (by
    calc r = x⁻¹ * (x * r * x⁻¹) * x := by group
      _ = x⁻¹ * (r₁ * x) := by rw [h1, mul_assoc]
      _ = x⁻¹ * (x * r₁) := by rw [hx.r_comm]
      _ = r₁ := by group)
  rcases mem_four h.cardR hR2 hr hx.r_mem hr1 hx.r_ne hrr₁ hxr with h1 | h1 | h1 | h1
  · exact absurd h1 hxr1
  · exact absurd h1 hxrr
  · exact absurd h1 hxrr₁
  · exact h1

omit hP hPC in
theorem outer_conj_V₀_of_ne {w : G} (hw : w ∈ V₀) (hw1 : w ≠ 1) (hwz : w ≠ z) :
    x * w * x⁻¹ = w * z := by
  have hV₀2 : ∀ y ∈ V₀, y * y = 1 := fun y hy => h.mul_self (h.V₀_le hy)
  have hxw : x * w * x⁻¹ ∈ V₀ :=
    (mem_normalizer_iff.mp (h.normalizer_le_normalizer_V₀ hx.normV) w).mp hw
  have hne1 : x * w * x⁻¹ ≠ 1 := fun h1 => hw1 (by
    calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group)
  have hnew : x * w * x⁻¹ ≠ w := fun h1 => by
    rcases hx.fix_V₀ w hw (by
      calc x * w = x * w * x⁻¹ * x := by group
        _ = w * x := by rw [h1]) with h2 | h2
    · exact hw1 h2
    · exact hwz h2
  have hnez : x * w * x⁻¹ ≠ z := fun h1 => hwz (by
    calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
      _ = x⁻¹ * (z * x) := by rw [h1, mul_assoc]
      _ = x⁻¹ * (x * z) := by rw [hx.z_comm]
      _ = z := by group)
  rcases mem_four h.card_V₀ hV₀2 hw hx.z_mem hw1 hx.z_ne hwz hxw with h1 | h1 | h1 | h1
  · exact absurd h1 hne1
  · exact absurd h1 hnew
  · exact absurd h1 hnez
  · exact h1

omit hP hPC in
theorem eq_one_or_eq_z {u : G} (hu : u ∈ V₀) (hux : u * (x * u * x⁻¹) = 1) : u = 1 ∨ u = z := by
  have hu2 : u * u = 1 := h.mul_self (h.V₀_le hu)
  have h1 : x * u * x⁻¹ = u := by
    calc x * u * x⁻¹ = u⁻¹ * (u * (x * u * x⁻¹)) := by group
      _ = u := by rw [hux, mul_one]; exact inv_eq_of_mul_eq_one_right hu2
  exact hx.fix_V₀ u hu (by
    calc x * u = x * u * x⁻¹ * x := by group
      _ = u * x := by rw [h1])

theorem exists_c₁ : ∃ c₁ ∈ P, c₁ ∉ R ⊔ T ∧ c₁ * c₁ = 1 ∧ x * c₁ * x⁻¹ = c₁ * z := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀2 : ∀ y ∈ V₀, y * y = 1 := fun y hy => h.mul_self (h.V₀_le hy)
  obtain ⟨c₀, hc₀, hc₀V, hc₀2, hu⟩ := h.exists_invol_fixed hP hPC hx
  set u := c₀⁻¹ * (x * c₀ * x⁻¹) with hudef
  have hxc₀ : x * c₀ * x⁻¹ = c₀ * u := by rw [hudef]; group
  have hux : u * (x * u * x⁻¹) = 1 := by
    have h1 : c₀ * 1 = c₀ * (u * (x * u * x⁻¹)) := by
      calc c₀ * 1 = (x * x) * c₀ * (x * x)⁻¹ := by rw [hx.sq]; group
        _ = x * (x * c₀ * x⁻¹) * x⁻¹ := by group
        _ = x * (c₀ * u) * x⁻¹ := by rw [hxc₀]
        _ = (x * c₀ * x⁻¹) * (x * u * x⁻¹) := by group
        _ = c₀ * (u * (x * u * x⁻¹)) := by rw [hxc₀]; group
    exact (mul_left_cancel h1).symm
  rcases h.eq_one_or_eq_z hx hu hux with h1 | h1
  ·
    obtain ⟨w₀, hw₀, hw₀1, hw₀z⟩ := exists_ne_one_ne h.card_V₀ hV₀2 hx.z_mem
    have hxw₀ := h.outer_conj_V₀_of_ne hx hw₀ hw₀1 hw₀z
    have hw₀P : w₀ ∈ P := hVP (h.V₀_le hw₀)
    refine ⟨c₀ * w₀, mul_mem hc₀ hw₀P, fun he => hc₀V ?_, ?_, ?_⟩
    · have := mul_mem he (inv_mem (h.V₀_le hw₀))
      rwa [mul_inv_cancel_right] at this
    · calc c₀ * w₀ * (c₀ * w₀) = c₀ * (w₀ * c₀) * w₀ := by group
        _ = c₀ * (c₀ * w₀) * w₀ := by rw [P_comm_V₀ hP hw₀ hc₀]
        _ = (c₀ * c₀) * (w₀ * w₀) := by group
        _ = 1 := by rw [hc₀2, hV₀2 w₀ hw₀, one_mul]
    · calc x * (c₀ * w₀) * x⁻¹ = (x * c₀ * x⁻¹) * (x * w₀ * x⁻¹) := by group
        _ = c₀ * w₀ * z := by rw [hxc₀, hxw₀, h1, mul_one, mul_assoc]
  · exact ⟨c₀, hc₀, hc₀V, hc₀2, by rw [hxc₀, h1]⟩

theorem commP_mul_eq_of_mType (hm : MType (R ⊔ T) P) {c₁ c : G} (hc₁ : c₁ ∈ P)
    (hc₁V : c₁ ∉ R ⊔ T) (hc₁2 : c₁ * c₁ = 1) (hc₁x : x * c₁ * x⁻¹ = c₁ * z) (hc : c ∈ P)
    (hcV : c ∉ R ⊔ T) (hc2 : c * c = 1) (hc₁c : c₁⁻¹ * c ∉ R ⊔ T) :
    ⁅c₁ * c, r₁⁆ = ⁅c₁, c⁆ := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hzV₀ : z ∈ V₀ := hx.z_mem
  have hzP : z ∈ P := hVP (h.V₀_le hzV₀)
  have hc₁i : c₁⁻¹ = c₁ := inv_eq_of_mul_eq_one_right hc₁2
  have hy : c₁ * c ∈ P := mul_mem hc₁ hc
  have hyV : c₁ * c ∉ R ⊔ T := fun he => hc₁c (by rwa [hc₁i])
  have hcc₁ := h.commP_mem hP hPC hc₁ hc
  obtain ⟨a, ha, hadef⟩ := h.exists_commP_eq hP hPC hy hyV hcc₁
  have haP : a ∈ P := hVP (mem_sup_left ha)
  have hc₁x' : c₁⁻¹ * (x * c₁ * x⁻¹) ∈ R ⊔ T := by
    rw [hc₁x, ← mul_assoc, inv_mul_cancel, one_mul]
    exact h.V₀_le hzV₀
  have hv₀ := h.outer_conj_mem_coset hP hPC hx hc₁ hc₁V hc₁x' hc hcV hc₁c
  obtain ⟨c', hc'def⟩ : ∃ c' : G, c' = x * c * x⁻¹ := ⟨_, rfl⟩
  rw [← hc'def] at hv₀
  obtain ⟨v, hvdef⟩ : ∃ v : G, v = (c₁ * c)⁻¹ * c' := ⟨_, rfl⟩
  have hv : v ∈ R ⊔ T := hvdef ▸ hv₀
  have hc' : c' = c₁ * c * v := by rw [hvdef]; group
  have hc'P : c' ∈ P := hc'def ▸ (mem_normalizer_iff.mp hx.normP c).mp hc
  have hvP : v ∈ P := hVP hv
  have hcv : ⁅c₁ * c, v⁆ = ⁅c₁, c⁆ := by
    have h1 : (c₁ * c * v) * (c₁ * c * v) = 1 := by
      rw [← hc', hc'def]
      calc x * c * x⁻¹ * (x * c * x⁻¹) = x * (c * c) * x⁻¹ := by group
        _ = 1 := by rw [hc2]; group
    rw [h.mul_self_mul_P hP hPC hy hvP, h.mul_self_mul_P hP hPC hc₁ hc, hc₁2, hc2,
      h.mul_self hv] at h1
    simp only [one_mul, mul_one] at h1
    have h2 := h.commP_mul_self hP hPC hc₁ hc
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_eq_of_mul_eq_one_right h2
  obtain ⟨r, hr, w, hw, hvrw⟩ := h.exists_mul hv
  have hrP : r ∈ P := hVP (mem_sup_left hr)
  have hwP : w ∈ P := hVP (h.V₀_le hw)
  have hcomm_r : ∀ y ∈ P, ⁅y, v⁆ = ⁅y, r⁆ := fun y hy' => by
    rw [hvrw, h.commP_mul_right hP hPC hy' hrP hwP, commP_V₀_right hP hy' hw, mul_one]
  have hra : r = a := h.commP_injective hP hPC hy hyV hr ha (by rw [← hcomm_r _ hy, hcv, hadef])
  subst hra
  have hc₁c' : c₁ * c' = c * v := by
    rw [hc', ← mul_assoc, ← mul_assoc, hc₁2, one_mul]
  have hcc' : c₁ * c' ∉ R ⊔ T := by
    rw [hc₁c']
    intro he
    apply hcV
    have := mul_mem he (inv_mem hv)
    rwa [mul_inv_cancel_right] at this
  have hpar₁ : ⁅c₁ * c', r⁆ = ⁅c, r⁆ := by
    rw [hc₁c', h.commP_mul_left hP hPC hc hvP hrP, h.commP_V_V hv (mem_sup_left hr), mul_one]
  have hpar₂ : ⁅c₁, c'⁆ = ⁅c, r⁆ := by
    have hX : ⁅c₁, r⁆ * ⁅c₁, r⁆ = 1 := h.commP_mul_self hP hPC hc₁ hrP
    have hcomm :=
      h.comm (h.V₀_le (h.commP_mem hP hPC hc₁ hrP)) (h.V₀_le (h.commP_mem hP hPC hc hrP))
    rw [hc', h.commP_mul_right hP hPC hc₁ hy hvP, h.commP_mul_right hP hPC hc₁ hc₁ hc,
      commutatorElement_self, one_mul, hcomm_r _ hc₁, ← hadef, h.commP_mul_left hP hPC hc₁ hc hrP,
      mul_assoc, ← hcomm, ← mul_assoc, hX, one_mul]
  have hxr : x * r * x⁻¹ ∈ R := (mem_normalizer_iff.mp hx.normR r).mp hr
  have hxrP : x * r * x⁻¹ ∈ P := hVP (mem_sup_left hxr)
  have hc₁c'P : c₁ * c' ∈ P := mul_mem hc₁ hc'P
  have e1 : x * ⁅c₁ * c, r⁆ * x⁻¹ = ⁅c₁ * c', x * r * x⁻¹⁆ := by
    have e0 : x * (c₁ * c) * x⁻¹ = c₁ * c' * z := by
      calc x * (c₁ * c) * x⁻¹ = (x * c₁ * x⁻¹) * (x * c * x⁻¹) := by group
        _ = c₁ * (z * c') := by rw [hc₁x, hc'def, mul_assoc]
        _ = c₁ * c' * z := by rw [← P_comm_V₀ hP hzV₀ hc'P, mul_assoc]
    rw [conj_commutatorElement, e0, h.commP_mul_left hP hPC hc₁c'P hzP hxrP,
      commP_V₀_left hP hzV₀ hxrP, mul_one]
  have e2 : x * ⁅c₁, c⁆ * x⁻¹ = ⁅c₁, c'⁆ := by
    rw [conj_commutatorElement, hc₁x, ← hc'def, h.commP_mul_left hP hPC hc₁ hzP hc'P,
      commP_V₀_left hP hzV₀ hc'P, mul_one]
  have hpar₃ : ⁅c₁ * c', x * r * x⁻¹⁆ = ⁅c₁, c'⁆ := by rw [← e1, hadef, e2]
  have hfix : x * r * x⁻¹ = r :=
    h.commP_injective hP hPC hc₁c'P hcc' hxr hr (by rw [hpar₃, hpar₂, hpar₁])
  rcases hx.fix_R r hr (by
    calc x * r = x * r * x⁻¹ * x := by group
      _ = r * x := by rw [hfix]) with h1 | h1
  · exfalso
    rw [h1, commutatorElement_one_right] at hadef
    exact hm c₁ hc₁ c hc hc₁V hcV hc₁2 hc2 hc₁c
      ((commutatorElement_eq_one_iff_mul_comm).mp hadef.symm)
  · rw [← h1]
    exact hadef

theorem exists_c₂ (hm : MType (R ⊔ T) P) (hP64 : Nat.card P = 64) {c₁ : G} (hc₁ : c₁ ∈ P)
    (hc₁V : c₁ ∉ R ⊔ T) (hc₁2 : c₁ * c₁ = 1) (hc₁x : x * c₁ * x⁻¹ = c₁ * z) :
    ∃ c₂ ∈ P, c₂ ∉ R ⊔ T ∧ c₂ * c₂ = 1 ∧ c₁⁻¹ * c₂ ∉ R ⊔ T ∧
      x * c₂ * x⁻¹ = c₁ * r₁ * c₂ * z := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀2 : ∀ y ∈ V₀, y * y = 1 := fun y hy => h.mul_self (h.V₀_le hy)
  have hzV₀ : z ∈ V₀ := hx.z_mem
  have hzP : z ∈ P := hVP (h.V₀_le hzV₀)
  have hr₁P : r₁ ∈ P := hVP (mem_sup_left hx.r_mem)
  have hc₁r : ⁅c₁, r₁⁆ = z := h.commP_eq_z hP hPC hx hc₁ hc₁V (by
    rw [hc₁x, ← mul_assoc, inv_mul_cancel, one_mul]; exact hzV₀)
  obtain ⟨w₀, hw₀, hw₀1, hw₀z⟩ := exists_ne_one_ne h.card_V₀ hV₀2 hzV₀
  obtain ⟨p, hp, hpw⟩ := h.exists_mem_P_transvHom hP hPC hP64 hx.r_mem hx.r_ne hw₀
  have hpr : ⁅p, r₁⁆ = w₀ := by
    have e : ⁅p, r₁⁆ = r₁ * (r₁⁻¹ * (p * r₁ * p⁻¹)) * r₁⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, hpw, P_comm_V₀ hP hw₀ hr₁P]
    group
  have hpV : p ∉ R ⊔ T := fun he => hw₀1 (by rw [← hpr, h.commP_V_V he (mem_sup_left hx.r_mem)])
  obtain ⟨v, hv, hpv⟩ := h.P_exists_invol hP hPC hp hpV
  set c := p * v with hcdef
  have hcP : c ∈ P := mul_mem hp (hVP hv)
  have hcV : c ∉ R ⊔ T := fun he => hpV (by
    have := mul_mem he (inv_mem hv)
    rwa [hcdef, mul_inv_cancel_right] at this)
  have hcr : ⁅c, r₁⁆ = w₀ := by
    rw [hcdef, h.commP_mul_left hP hPC hp (hVP hv) hr₁P, h.commP_V_V hv (mem_sup_left hx.r_mem),
      mul_one, hpr]
  have hc₁c : c₁⁻¹ * c ∉ R ⊔ T := by
    intro he
    apply hw₀z
    rw [← hcr, ← hc₁r]
    have h1 : ⁅c₁⁻¹ * c, r₁⁆ = 1 := h.commP_V_V he (mem_sup_left hx.r_mem)
    have hc₁i : c₁⁻¹ = c₁ := inv_eq_of_mul_eq_one_right hc₁2
    rw [hc₁i, h.commP_mul_left hP hPC hc₁ hcP hr₁P] at h1
    calc ⁅c, r₁⁆ = ⁅c₁, r₁⁆ * (⁅c₁, r₁⁆ * ⁅c, r₁⁆) := by
          rw [← mul_assoc, h.commP_mul_self hP hPC hc₁ hr₁P, one_mul]
      _ = ⁅c₁, r₁⁆ := by rw [h1, mul_one]
  have hpar := h.commP_mul_eq_of_mType hP hPC hx hm hc₁ hc₁V hc₁2 hc₁x hcP hcV hpv hc₁c
  have hb : c₁ * r₁ * c ∈ P := mul_mem (mul_mem hc₁ hr₁P) hcP
  have hb2 : c₁ * r₁ * c * (c₁ * r₁ * c) = 1 := by
    rw [h.mul_self_mul_P hP hPC (mul_mem hc₁ hr₁P) hcP, h.mul_self_mul_P hP hPC hc₁ hr₁P, hc₁2,
      h.mul_self (mem_sup_left hx.r_mem), hpv]
    simp only [one_mul, mul_one]
    rw [h.commP_mul_left hP hPC hc₁ hr₁P hcP, h.commP_swap hP hPC hcP hr₁P, ← hpar,
      h.commP_mul_left hP hPC hc₁ hcP hr₁P, hc₁r]
    have hz2 := hV₀2 z hzV₀
    have hw2 : ⁅c, r₁⁆ * ⁅c, r₁⁆ = 1 := h.commP_mul_self hP hPC hcP hr₁P
    have hcomm := h.comm (h.V₀_le hzV₀) (h.V₀_le (h.commP_mem hP hPC hcP hr₁P))
    calc z * (z * ⁅c, r₁⁆ * ⁅c, r₁⁆) = (z * z) * (⁅c, r₁⁆ * ⁅c, r₁⁆) := by group
      _ = 1 := by rw [hz2, hw2, one_mul]
  have hc₁i : c₁⁻¹ = c₁ := inv_eq_of_mul_eq_one_right hc₁2
  have hr₁i : r₁⁻¹ = r₁ := inv_eq_of_mul_eq_one_right (h.mul_self (mem_sup_left hx.r_mem))
  have hVc : ∀ {u y : G}, u ∈ P → y ∈ R ⊔ T → u * y * u⁻¹ ∈ R ⊔ T := fun hu hy =>
    (mem_normalizer_iff.mp (hP.le hu).1 _).mp hy
  have hcrc : c⁻¹ * r₁ * c ∈ R ⊔ T := by
    have := hVc (inv_mem hcP) (mem_sup_left hx.r_mem)
    rwa [inv_inv] at this
  have hbV : c₁ * r₁ * c ∉ R ⊔ T := by
    intro he
    apply hc₁c
    have e : c₁⁻¹ * c = (c₁ * r₁ * c) * (c⁻¹ * r₁ * c)⁻¹ := by rw [hc₁i, ← hr₁i]; group
    rw [e]
    exact mul_mem he (inv_mem hcrc)
  have hcx := h.outer_conj_mem_coset hP hPC hx hc₁ hc₁V (by
    rw [hc₁x, ← mul_assoc, inv_mul_cancel, one_mul]; exact h.V₀_le hzV₀) hcP hcV hc₁c
  set e := (c₁ * r₁ * c)⁻¹ * (x * c * x⁻¹) with hedef
  have hxc : x * c * x⁻¹ = c₁ * r₁ * c * e := by rw [hedef]; group
  have heV : e ∈ R ⊔ T := by
    have e' : e = (c⁻¹ * r₁⁻¹ * c) * ((c₁ * c)⁻¹ * (x * c * x⁻¹)) := by rw [hedef]; group
    rw [e', hr₁i]
    exact mul_mem hcrc hcx
  have he₀ : e ∈ V₀ := by
    refine h.P_invol_coset hP hPC hb hbV hb2 heV ?_
    rw [← hxc]
    calc x * c * x⁻¹ * (x * c * x⁻¹) = x * (c * c) * x⁻¹ := by group
      _ = 1 := by rw [hpv]; group
  have hxb : x * (c₁ * r₁ * c) * x⁻¹ = c * e := by
    have hc₁r₁ : c₁ * r₁ * c₁ * r₁ = z := by
      rw [← hc₁r, commutatorElement_def, hc₁i, hr₁i]
    calc x * (c₁ * r₁ * c) * x⁻¹ = (x * c₁ * x⁻¹) * (x * r₁ * x⁻¹) * (x * c * x⁻¹) := by group
      _ = c₁ * z * r₁ * (c₁ * r₁ * c * e) := by rw [hc₁x, outer_conj_r hx, hxc]
      _ = c₁ * (z * (r₁ * c₁ * r₁)) * c * e := by group
      _ = c₁ * ((r₁ * c₁ * r₁) * z) * c * e := by
          rw [P_comm_V₀ hP hzV₀ (mul_mem (mul_mem hr₁P hc₁) hr₁P)]
      _ = (c₁ * r₁ * c₁ * r₁) * z * c * e := by group
      _ = c * e := by rw [hc₁r₁, hV₀2 z hzV₀, one_mul]
  have hee : e * (x * e * x⁻¹) = 1 := by
    have h1 : c * 1 = c * (e * (x * e * x⁻¹)) := by
      calc c * 1 = (x * x) * c * (x * x)⁻¹ := by rw [hx.sq]; group
        _ = x * (x * c * x⁻¹) * x⁻¹ := by group
        _ = x * (c₁ * r₁ * c * e) * x⁻¹ := by rw [hxc]
        _ = (x * (c₁ * r₁ * c) * x⁻¹) * (x * e * x⁻¹) := by group
        _ = c * (e * (x * e * x⁻¹)) := by rw [hxb]; group
    exact (mul_left_cancel h1).symm
  rcases h.eq_one_or_eq_z hx he₀ hee with h1 | h1
  ·
    have hxw₀ := h.outer_conj_V₀_of_ne hx hw₀ hw₀1 hw₀z
    have hw₀P : w₀ ∈ P := hVP (h.V₀_le hw₀)
    refine ⟨c * w₀, mul_mem hcP hw₀P, fun he => hcV ?_, ?_, fun he => hc₁c ?_, ?_⟩
    · have := mul_mem he (inv_mem (h.V₀_le hw₀))
      rwa [mul_inv_cancel_right] at this
    · calc c * w₀ * (c * w₀) = c * (w₀ * c) * w₀ := by group
        _ = c * (c * w₀) * w₀ := by rw [P_comm_V₀ hP hw₀ hcP]
        _ = (c * c) * (w₀ * w₀) := by group
        _ = 1 := by rw [hpv, hV₀2 w₀ hw₀, one_mul]
    · have := mul_mem he (inv_mem (h.V₀_le hw₀))
      rwa [← mul_assoc, mul_inv_cancel_right] at this
    · calc x * (c * w₀) * x⁻¹ = (x * c * x⁻¹) * (x * w₀ * x⁻¹) := by group
        _ = c₁ * r₁ * (c * w₀) * z := by rw [hxc, h1, hxw₀]; group
  · exact ⟨c, hcP, hcV, hpv, hc₁c, by rw [hxc, h1]⟩

theorem exists_sGens (hm : MType (R ⊔ T) P) (hP64 : Nat.card P = 64) :
    ∃ q : SGens G, q.t = x ∧ q.a = r₁ ∧ q.g₁ ∈ P ∧ q.g₂ ∈ P ∧ q.σ ∈ R ∧ q.σ ≠ 1 ∧
      q.σ ≠ r₁ ∧ q.g₁ * q.g₁ = z ∧ q.g₂ * q.g₂ ∈ V₀ ∧ q.g₂ * q.g₂ ≠ 1 ∧
      q.g₂ * q.g₂ ≠ z := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀2 : ∀ y ∈ V₀, y * y = 1 := fun y hy => h.mul_self (h.V₀_le hy)
  have hzV₀ : z ∈ V₀ := hx.z_mem
  have hzP : z ∈ P := hVP (h.V₀_le hzV₀)
  have hr₁P : r₁ ∈ P := hVP (mem_sup_left hx.r_mem)
  have hr₁2 : r₁ * r₁ = 1 := h.mul_self (mem_sup_left hx.r_mem)
  obtain ⟨c₁, hc₁, hc₁V, hc₁2, hc₁x⟩ := h.exists_c₁ hP hPC hx
  obtain ⟨c₂, hc₂, hc₂V, hc₂2, hc₁₂, hc₂x⟩ := h.exists_c₂ hP hPC hx hm hP64 hc₁ hc₁V hc₁2 hc₁x
  have hc₁r : ⁅c₁, r₁⁆ = z := h.commP_eq_z hP hPC hx hc₁ hc₁V (by
    rw [hc₁x, ← mul_assoc, inv_mul_cancel, one_mul]; exact hzV₀)
  set w := ⁅c₂, r₁⁆ with hwdef
  have hwV₀ : w ∈ V₀ := h.commP_mem hP hPC hc₂ hr₁P
  have hw1 : w ≠ 1 := fun he => hc₂V (h.mem_V_of_commP_eq_one hP hPC hc₂ hx.r_mem hx.r_ne he)
  have hwz : w ≠ z := fun he => hc₁₂
    (h.inv_mul_mem_V_of_commP_eq hP hPC hc₁ hc₂ hx.r_mem hx.r_ne (by rw [hc₁r, ← he]))
  obtain ⟨σ, hσ, hσw⟩ := h.exists_commP_eq hP hPC hc₁ hc₁V hwV₀
  have hσP : σ ∈ P := hVP (mem_sup_left hσ)
  have hσ1 : σ ≠ 1 := fun he => hw1 (by rw [← hσw, he, commutatorElement_one_right])
  have hσr : σ ≠ r₁ := fun he => hwz (by rw [← hσw, he, hc₁r])
  have hσ2 : σ * σ = 1 := h.mul_self (mem_sup_left hσ)
  have hpar := h.commP_mul_eq_of_mType hP hPC hx hm hc₁ hc₁V hc₁2 hc₁x hc₂ hc₂V hc₂2 hc₁₂
  have hg₁P : c₁ * r₁ ∈ P := mul_mem hc₁ hr₁P
  have hg₂P : c₂ * r₁ ∈ P := mul_mem hc₂ hr₁P
  have hg₁2 : c₁ * r₁ * (c₁ * r₁) = z := by
    rw [h.mul_self_mul_P hP hPC hc₁ hr₁P, hc₁2, hr₁2, one_mul, one_mul, hc₁r]
  have hg₂2 : c₂ * r₁ * (c₂ * r₁) = w := by
    rw [h.mul_self_mul_P hP hPC hc₂ hr₁P, hc₂2, hr₁2, one_mul, one_mul]
  have hpow4 : ∀ {y u : G}, y * y = u → u * u = 1 → y ^ 4 = 1 := fun {y u} hy hu => by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hy, hu]
  have hpow3 : ∀ {y : G}, y ^ 4 = 1 → y ^ 3 = y⁻¹ := fun {y} hy => by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hy]
  have hg₁4 := hpow4 hg₁2 (hV₀2 z hzV₀)
  have hg₂4 := hpow4 hg₂2 (hV₀2 w hwV₀)
  have hc₁i : c₁⁻¹ = c₁ := inv_eq_of_mul_eq_one_right hc₁2
  have hc₂i : c₂⁻¹ = c₂ := inv_eq_of_mul_eq_one_right hc₂2
  have hr₁i : r₁⁻¹ = r₁ := inv_eq_of_mul_eq_one_right hr₁2
  have hcen : ∀ {y u : G}, y ∈ V₀ → u ∈ P → y * u = u * y := fun hy hu =>
    (P_comm_V₀ hP hy hu).symm
  have hg₁g₂ : c₁ * r₁ * (c₂ * r₁) = c₂ * r₁ * (c₁ * r₁) := by
    apply (commutatorElement_eq_one_iff_mul_comm).mp
    rw [h.commP_mul_left hP hPC hc₁ hr₁P hg₂P, h.commP_mul_right hP hPC hc₁ hc₂ hr₁P,
      h.commP_mul_right hP hPC hr₁P hc₂ hr₁P, commutatorElement_self, mul_one,
      h.commP_swap hP hPC hc₂ hr₁P, ← hpar, h.commP_mul_left hP hPC hc₁ hc₂ hr₁P, hc₁r, ← hwdef]
    have hz2 := hV₀2 z hzV₀
    have hw2 := hV₀2 w hwV₀
    have hzw := h.comm (h.V₀_le hzV₀) (h.V₀_le hwV₀)
    calc z * w * z * w = z * (w * z) * w := by group
      _ = z * (z * w) * w := by rw [hzw]
      _ = (z * z) * (w * w) := by group
      _ = 1 := by rw [hz2, hw2, one_mul]
  have hs : ⁅c₂, σ⁆ = z * w := by
    set u := ⁅c₂, σ⁆ with hudef
    have huV₀ : u ∈ V₀ := h.commP_mem hP hPC hc₂ hσP
    have hxσ := h.outer_conj_R_of_ne hx hσ hσ1 hσr
    have hxu : x * u * x⁻¹ = z * u := by
      rw [hudef, conj_commutatorElement, hc₂x, hxσ,
        h.commP_mul_left hP hPC (mul_mem (mul_mem hc₁ hr₁P) hc₂) hzP (mul_mem hσP hr₁P),
        commP_V₀_left hP hzV₀ (mul_mem hσP hr₁P), mul_one,
        h.commP_mul_left hP hPC (mul_mem hc₁ hr₁P) hc₂ (mul_mem hσP hr₁P),
        h.commP_mul_left hP hPC hc₁ hr₁P (mul_mem hσP hr₁P),
        h.commP_V_V (mem_sup_left hx.r_mem) (mem_sup_left (mul_mem hσ hx.r_mem)), mul_one,
        h.commP_mul_right hP hPC hc₁ hσP hr₁P, hσw, hc₁r,
        h.commP_mul_right hP hPC hc₂ hσP hr₁P, ← hudef, ← hwdef]
      have hw2 := hV₀2 w hwV₀
      have hwz' := h.comm (h.V₀_le hwV₀) (h.V₀_le hzV₀)
      have hwu := h.comm (h.V₀_le hwV₀) (h.V₀_le huV₀)
      calc w * z * (u * w) = z * (w * u) * w := by rw [hwz']; group
        _ = z * (u * w) * w := by rw [hwu]
        _ = z * u * (w * w) := by group
        _ = z * u := by rw [hw2, mul_one]
    have hu1 : u ≠ 1 := fun he => by
      rw [he, mul_one, mul_one, mul_inv_cancel] at hxu
      exact hx.z_ne hxu.symm
    have huz : u ≠ z := fun he => by
      rw [he, outer_conj_z hx, hV₀2 z hzV₀] at hxu
      exact hx.z_ne hxu
    have huw : u ≠ w := fun he => hσr
      (h.commP_injective hP hPC hc₂ hc₂V hσ hx.r_mem (by rw [← hudef, he]))
    rcases mem_four h.card_V₀ hV₀2 hzV₀ hwV₀ hx.z_ne hw1 hwz.symm huV₀ with h1 | h1 | h1 | h1
    · exact absurd h1 hu1
    · exact absurd h1 huz
    · exact absurd h1 huw
    · exact h1
  have ha₁ : r₁ * (c₁ * r₁) * r₁⁻¹ = (c₁ * r₁) ^ 3 := by
    rw [hpow3 hg₁4, mul_inv_rev, hc₁i, hr₁i]
    calc r₁ * (c₁ * r₁) * r₁ = r₁ * c₁ * (r₁ * r₁) := by group
      _ = r₁ * c₁ := by rw [hr₁2, mul_one]
  have ha₂ : r₁ * (c₂ * r₁) * r₁⁻¹ = (c₂ * r₁) ^ 3 := by
    rw [hpow3 hg₂4, mul_inv_rev, hc₂i, hr₁i]
    calc r₁ * (c₂ * r₁) * r₁ = r₁ * c₂ * (r₁ * r₁) := by group
      _ = r₁ * c₂ := by rw [hr₁2, mul_one]
  have hσ₁ : σ * (c₁ * r₁) * σ⁻¹ = c₁ * r₁ * (c₂ * r₁) ^ 2 := by
    have e : σ * (c₁ * r₁) * σ⁻¹ = ⁅σ, c₁ * r₁⁆ * (c₁ * r₁) := by
      simp only [commutatorElement_def]; group
    rw [e, h.commP_swap hP hPC hg₁P hσP, h.commP_mul_left hP hPC hc₁ hr₁P hσP, hσw,
      h.commP_V_V (mem_sup_left hx.r_mem) (mem_sup_left hσ), mul_one, sq, hg₂2,
      hcen hwV₀ hg₁P]
  have hσ₂ : σ * (c₂ * r₁) * σ⁻¹ = (c₁ * r₁) ^ 2 * (c₂ * r₁) ^ 3 := by
    have e : σ * (c₂ * r₁) * σ⁻¹ = ⁅σ, c₂ * r₁⁆ * (c₂ * r₁) := by
      simp only [commutatorElement_def]; group
    rw [e, h.commP_swap hP hPC hg₂P hσP, h.commP_mul_left hP hPC hc₂ hr₁P hσP, hs,
      h.commP_V_V (mem_sup_left hx.r_mem) (mem_sup_left hσ), mul_one, sq, hg₁2,
      pow_three (c₂ * r₁), hg₂2]
    calc z * w * (c₂ * r₁) = z * (w * (c₂ * r₁)) := by group
      _ = z * (c₂ * r₁ * w) := by rw [hcen hwV₀ hg₂P]
  have ht₁ : x * (c₁ * r₁) * x⁻¹ = (c₁ * r₁) ^ 3 := by
    rw [pow_three (c₁ * r₁), hg₁2,
      show x * (c₁ * r₁) * x⁻¹ = (x * c₁ * x⁻¹) * (x * r₁ * x⁻¹) by group, hc₁x,
      outer_conj_r hx]
    calc c₁ * z * r₁ = c₁ * (z * r₁) := by group
      _ = c₁ * (r₁ * z) := by rw [hcen hzV₀ hr₁P]
      _ = c₁ * r₁ * z := by group
  have ht₂ : x * (c₂ * r₁) * x⁻¹ = (c₁ * r₁) ^ 3 * (c₂ * r₁) := by
    rw [pow_three (c₁ * r₁), hg₁2,
      show x * (c₂ * r₁) * x⁻¹ = (x * c₂ * x⁻¹) * (x * r₁ * x⁻¹) by group, hc₂x,
      outer_conj_r hx]
    calc c₁ * r₁ * c₂ * z * r₁ = c₁ * r₁ * c₂ * (z * r₁) := by group
      _ = c₁ * r₁ * c₂ * (r₁ * z) := by rw [hcen hzV₀ hr₁P]
      _ = c₁ * r₁ * (c₂ * r₁ * z) := by group
      _ = c₁ * r₁ * (z * (c₂ * r₁)) := by rw [hcen hzV₀ hg₂P]
      _ = c₁ * r₁ * z * (c₂ * r₁) := by group
  have htσ : x * σ * x⁻¹ = r₁ * σ := by
    rw [h.outer_conj_R_of_ne hx hσ hσ1 hσr]
    exact h.comm (mem_sup_left hσ) (mem_sup_left hx.r_mem)
  let q₀ : P0Gens G := ⟨c₁ * r₁, c₂ * r₁, r₁, σ, hr₁2, hσ2,
    h.comm (mem_sup_left hx.r_mem) (mem_sup_left hσ), hg₁4, hg₂4, hg₁g₂, ha₁, ha₂, hσ₁, hσ₂⟩
  refine ⟨⟨q₀, x, hx.sq, ht₁, ht₂, outer_conj_r hx, htσ⟩, rfl, rfl, hg₁P, hg₂P, hσ, hσ1, hσr,
    hg₁2, (by rw [hg₂2]; exact hwV₀ : c₂ * r₁ * (c₂ * r₁) ∈ V₀),
    (by rw [hg₂2]; exact hw1 : c₂ * r₁ * (c₂ * r₁) ≠ 1),
    (by rw [hg₂2]; exact hwz : c₂ * r₁ * (c₂ * r₁) ≠ z)⟩

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
