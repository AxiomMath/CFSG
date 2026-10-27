module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S2B

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

theorem mem_cenMod_of_comm {G : Type*} [Group G] [Finite G] {N M : Subgroup G} (hNM : N ≤ M)
    {x : G} (hx : ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ ∈ N) : x ∈ cenMod N M := by
  refine ⟨mem_normalizer_fintype fun n hn => ?_, hx⟩
  have := mul_mem (hx n (hNM hn)) hn
  rwa [inv_mul_cancel_right] at this

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem X₄Y_le_D₀ (h : d.Hyp) : d.X₄ ⊔ d.Y ≤ d.D₀ :=
  sup_le ((d.pull_mono X₄sub_le_A₂sub).trans h.A₂_le_D₀) Y_le_D₀

theorem conj_mem_X₄Y_of_mem_D₀ (h : d.Hyp) {p q : G} (hp : p ∈ d.D₀) (hq : q ∈ d.X₄ ⊔ d.Y) :
    p⁻¹ * q * p ∈ d.X₄ ⊔ d.Y := by
  have h1 := h.comm_D₀ (inv_mem hp) (h.X₄Y_le_D₀ hq)
  rw [inv_inv] at h1
  rw [show p⁻¹ * q * p = (p⁻¹ * q * p * q⁻¹) * q by group]
  exact mul_mem (mem_sup_right h1) hq

theorem S_comm_D₀_mem (h : d.Hyp) {s p : G} (hs : s ∈ d.S) (hp : p ∈ d.D₀) :
    s * p * s⁻¹ * p⁻¹ ∈ d.X₄ ⊔ d.Y := by
  rw [h.D₀_eq] at hp
  obtain ⟨a, ha, e, he, rfl⟩ := (h.mem_A₂E₂_iff).1 hp
  have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
  have h1 : s * a * s⁻¹ * a⁻¹ ∈ d.X₄ ⊔ d.F := by
    rw [← commutator_S_eq]
    exact commutator_mem_commutator hs (d.A₂_le_S ha)
  have h2 : s * e * s⁻¹ * e⁻¹ ∈ d.Y :=
    mul_mem ((mem_normalizer_iff.1 (h.S_le_normalizer_Y hs) e).1 heY) (inv_mem heY)
  have h3 : a * (s * e * s⁻¹ * e⁻¹) * a⁻¹ = s * e * s⁻¹ * e⁻¹ := by
    rw [Y_comm_D₀ h2 (h.A₂_le_D₀ ha) |>.symm, mul_inv_cancel_right]
  rw [show s * (a * e) * s⁻¹ * (a * e)⁻¹ =
    (s * a * s⁻¹ * a⁻¹) * (a * (s * e * s⁻¹ * e⁻¹) * a⁻¹) by group, h3]
  exact mul_mem ((sup_le_sup_left h.F_le_Y _) h1) (mem_sup_right h2)

theorem R_le_cenMod_D₀ (h : d.Hyp) : d.R ≤ cenMod (d.X₄ ⊔ d.Y) d.D₀ := by
  refine sup_le (fun s hs => mem_cenMod_of_comm h.X₄Y_le_D₀ fun p hp => h.S_comm_D₀_mem hs hp)
    (zpowers_le.2 (mem_cenMod_of_comm h.X₄Y_le_D₀ fun p hp => ?_))
  have hc := h.crossed_t_mem_Y hp
  have hcomm := Y_comm_D₀ hc (inv_mem hp)
  have e : d.t * p * d.t⁻¹ * p⁻¹ = p⁻¹ * (d.t * p * d.t) := by
    have e1 : d.t * p * d.t⁻¹ * p⁻¹ = p * ((p⁻¹ * (d.t * p * d.t)) * p⁻¹) := by
      rw [h.t_inv]
      group
    rw [e1, hcomm]
    group
  rw [e]
  exact mem_sup_right hc

theorem D₂_le_cenMod_D₀' (h : d.Hyp) : d.D₂ ≤ cenMod (d.X₄ ⊔ d.Y) d.D₀ := fun u hu =>
  mem_cenMod_of_comm h.X₄Y_le_D₀ fun p hp => mem_sup_right ((h.D₂_le_cenMod_D₀ hu).2 p hp)

theorem RD₂_le_cenMod_D₀ (h : d.Hyp) : d.R ⊔ d.D₂ ≤ cenMod (d.X₄ ⊔ d.Y) d.D₀ :=
  sup_le h.R_le_cenMod_D₀ h.D₂_le_cenMod_D₀'

theorem crossed_inv_eq (h : d.Hyp) (u : G) :
    u⁻¹ * d.t * u⁻¹⁻¹ * d.t = u⁻¹ * (u * d.t * u⁻¹ * d.t)⁻¹ * u := by
  have e : (u * d.t * u⁻¹ * d.t)⁻¹ = d.t⁻¹ * u * d.t⁻¹ * u⁻¹ := by group
  rw [e, h.t_inv]
  group

theorem crossed_eq_one_of_comm (h : d.Hyp) {r : G} (hr : r * d.t = d.t * r) :
    r * d.t * r⁻¹ * d.t = 1 := by
  rw [hr]
  group
  exact h.t_mul_t

theorem crossed_mul_of_mem_R (h : d.Hyp) {r : G} (hr : r ∈ d.R) (e : G) :
    r * e * d.t * (r * e)⁻¹ * d.t = r * (e * d.t * e⁻¹ * d.t) * r⁻¹ := by
  rw [h.crossed_mul_eq r e, h.crossed_eq_one_of_comm (mem_centralizer_singleton_iff.1
    (h.R_le_H hr)), mul_one]

theorem R_le_R₃ (h : d.Hyp) : d.R ≤ d.R₃ := by
  rw [h.R₃_eq]
  exact le_sup_left.trans le_sup_left

theorem Y_le_R₃ (h : d.Hyp) : d.Y ≤ d.R₃ := by
  rw [h.R₃_eq]
  exact le_sup_right.trans le_sup_left

theorem D₃_le_R₃ (h : d.Hyp) : d.D₃ ≤ d.R₃ := by
  rw [h.R₃_eq]
  exact le_sup_right

theorem mem_R₃_of_mem_D₂_of_crossed_mem (h : d.Hyp) {x : G} (hx : x ∈ d.D₂)
    (hθ : x * d.t * x⁻¹ * d.t ∈ d.X₄ ⊔ d.Y) : x ∈ d.R₃ := by
  obtain ⟨a, ha, y, hy, hay⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha y hy => (Y_comm_D₀ hy (h.A₂_le_D₀ (d.pull_mono X₄sub_le_A₂sub ha))).symm) hθ
  obtain ⟨u, hu, w, hw, huw⟩ := h.exists_D₃_conj_t (mem_sup_right ha : a ∈ d.X₃ ⊔ d.X₄)
  have huR₃ : u ∈ d.R₃ := h.D₃_le_R₃ hu
  have hxX : x ∈ d.XC₀ := D₂_le_XC₀ hx
  have huX : u ∈ d.XC₀ := h.D₃_le_XC₀ hu
  have hθg : x * u⁻¹ * d.t * (x * u⁻¹)⁻¹ * d.t ∈ d.Y := by
    have hux : u⁻¹ ∈ cenMod d.Y d.X₄ := inv_mem (h.R₃_le_cenMod huR₃)
    have hxc : x ∈ cenMod d.Y d.D₀ := h.D₂_le_cenMod_D₀ hx
    have ha' : a⁻¹ ∈ d.X₄ := inv_mem ha
    have haD : a⁻¹ ∈ d.D₀ := h.A₂_le_D₀ (d.pull_mono X₄sub_le_A₂sub ha')
    have e_a : u⁻¹ * a⁻¹ * u * a ∈ d.Y := by
      have := hux.2 a⁻¹ ha'
      rwa [inv_inv, inv_inv] at this
    have hw' : w⁻¹ ∈ d.Y := inv_mem (d.W_le_Y hw)
    have e_w : u⁻¹ * w⁻¹ * u ∈ d.Y := by
      have := (mem_normalizer_iff.1 hux.1 _).1 hw'
      rwa [inv_inv] at this
    have c₂ : x * a⁻¹ * x⁻¹ * a ∈ d.Y := by
      have := hxc.2 a⁻¹ haD
      rwa [inv_inv] at this
    have hy₁ : x * ((u⁻¹ * w⁻¹ * u) * (u⁻¹ * a⁻¹ * u * a)) * x⁻¹ ∈ d.Y :=
      (mem_normalizer_iff.1 hxc.1 _).1 (mul_mem e_w e_a)
    rw [h.crossed_mul_eq x u⁻¹, h.crossed_inv_eq u, huw, ← hay]
    rw [show x * (u⁻¹ * (a * w)⁻¹ * u) * x⁻¹ * (a * y) =
      (x * ((u⁻¹ * w⁻¹ * u) * (u⁻¹ * a⁻¹ * u * a)) * x⁻¹) * (x * a⁻¹ * x⁻¹ * a) * y by group]
    exact mul_mem (mul_mem hy₁ c₂) hy
  have hgX : x * u⁻¹ ∈ d.XC₀ := mul_mem hxX (inv_mem huX)
  have hgN := h.mem_NHA₂Y_of_crossed_mem hgX hθg
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.A₂ : Set G) ⊓ d.H) d.Y
    h.NHA₂_le_normalizer_Y
  obtain ⟨m, hm, y', hy', hmy⟩ : x * u⁻¹ ∈ ((normalizer (d.A₂ : Set G) ⊓ d.H : Subgroup G) :
      Set G) * (d.Y : Set G) := by
    rw [← hset]
    exact hgN
  have hmy' : m * y' = x * u⁻¹ := hmy
  have hmP : m ∈ (d.R₃ ⊔ d.D₂) ⊓ d.H := by
    refine Subgroup.mem_inf.2 ⟨?_, hm.2⟩
    rw [show m = x * u⁻¹ * y'⁻¹ by rw [← hmy']; group]
    exact mul_mem (mul_mem (mem_sup_right hx) (mem_sup_left (inv_mem huR₃)))
      (mem_sup_left (inv_mem (h.Y_le_R₃ hy')))
  have hmR := h.R₃D₂_inf_H_le_R hmP
  rw [show x = m * y' * u by rw [hmy']; group]
  exact mul_mem (mul_mem (h.R_le_R₃ hmR) (h.Y_le_R₃ hy')) huR₃

theorem mem_R₃_iff_of_mem_D₂ (h : d.Hyp) {x : G} (hx : x ∈ d.D₂) :
    x ∈ d.R₃ ↔ x * d.t * x⁻¹ * d.t ∈ d.X₄ ⊔ d.Y := by
  refine ⟨fun hxR => ?_, h.mem_R₃_of_mem_D₂_of_crossed_mem hx⟩
  exact (sup_le (sup_le le_sup_left (h.F_le_Y.trans le_sup_right))
    (h.V₂_le_Y.trans le_sup_right) : (d.X₄ ⊔ d.F) ⊔ d.V₂ ≤ d.X₄ ⊔ d.Y)
    (h.crossed_mem_of_mem_normalizer_R₂ (oTwo_le _ hxR))

theorem mem_R₃_iff_of_mem_R_sup_D₂ (h : d.Hyp) {x : G} (hx : x ∈ d.R ⊔ d.D₂) :
    x ∈ d.R₃ ↔ x * d.t * x⁻¹ * d.t ∈ d.X₄ ⊔ d.Y := by
  have hset := coe_mul_of_left_le_normalizer_right d.R d.D₂ h.R_le_normalizer_D₂
  obtain ⟨r, hr, e, he, rfl⟩ : x ∈ (d.R : Set G) * (d.D₂ : Set G) := by
    rw [← hset]
    exact hx
  rw [h.crossed_mul_of_mem_R hr]
  have hrn := (h.R_le_cenMod_D₀ hr).1
  have hre : r * e ∈ d.R₃ ↔ e ∈ d.R₃ :=
    ⟨fun hh => by simpa using mul_mem (inv_mem (h.R_le_R₃ hr)) hh,
      fun hh => mul_mem (h.R_le_R₃ hr) hh⟩
  rw [hre, h.mem_R₃_iff_of_mem_D₂ he]
  constructor
  · intro hθ
    exact (mem_normalizer_iff.1 hrn _).1 hθ
  · intro hθ
    have := (mem_normalizer_iff.1 (inv_mem hrn) _).1 hθ
    rwa [show r⁻¹ * (r * (e * d.t * e⁻¹ * d.t) * r⁻¹) * r⁻¹⁻¹ = e * d.t * e⁻¹ * d.t by group]
      at this

theorem crossed_conj_eq (h : d.Hyp) (u x : G) :
    (u * x * u⁻¹) * d.t * (u * x * u⁻¹)⁻¹ * d.t =
      ((u * x * u⁻¹) * (u * d.t * u⁻¹ * d.t)⁻¹ * (u * x * u⁻¹)⁻¹) *
        (u * (x * d.t * x⁻¹ * d.t) * u⁻¹) * (u * d.t * u⁻¹ * d.t) := by
  have e1 := h.crossed_mul_eq u (x * u⁻¹)
  have e2 := h.crossed_mul_eq x u⁻¹
  have e3 := h.crossed_inv_eq u
  rw [e2, e3] at e1
  calc (u * x * u⁻¹) * d.t * (u * x * u⁻¹)⁻¹ * d.t
      = u * (x * u⁻¹) * d.t * (u * (x * u⁻¹))⁻¹ * d.t := by group
    _ = _ := e1
    _ = _ := by group

theorem conj_inv_mul_mem (h : d.Hyp) {c p q : G} (hc : c ∈ cenMod (d.X₄ ⊔ d.Y) d.D₀)
    (hp : p ∈ d.D₀) (hq : q ∈ d.X₄ ⊔ d.Y) : c * p⁻¹ * c⁻¹ * q * p ∈ d.X₄ ⊔ d.Y := by
  have h1 : c * p⁻¹ * c⁻¹ * p ∈ d.X₄ ⊔ d.Y := by
    have := hc.2 p⁻¹ (inv_mem hp)
    rwa [inv_inv] at this
  rw [show c * p⁻¹ * c⁻¹ * q * p = (c * p⁻¹ * c⁻¹ * p) * (p⁻¹ * q * p) by group]
  exact mul_mem h1 (h.conj_mem_X₄Y_of_mem_D₀ hp hq)

theorem crossed_conj_mem (h : d.Hyp) {u x : G} (hu : u ∈ d.D₂) (hx : x ∈ d.R ⊔ d.D₂)
    (hθ : x * d.t * x⁻¹ * d.t ∈ d.X₄ ⊔ d.Y) :
    (u * x * u⁻¹) * d.t * (u * x * u⁻¹)⁻¹ * d.t ∈ d.X₄ ⊔ d.Y := by
  rw [h.crossed_conj_eq u x]
  have hp : u * d.t * u⁻¹ * d.t ∈ d.D₀ := h.crossed_mem_D₀ (D₂_le_XC₀ hu)
  have hc : u * x * u⁻¹ ∈ d.R ⊔ d.D₂ :=
    mul_mem (mul_mem (mem_sup_right hu) hx) (inv_mem (mem_sup_right hu))
  exact h.conj_inv_mul_mem (h.RD₂_le_cenMod_D₀ hc) hp
    ((mem_normalizer_iff.1 (h.D₂_le_cenMod_D₀' hu).1 _).1 hθ)

theorem D₂_le_normalizer_R₃ (h : d.Hyp) : d.D₂ ≤ normalizer (d.R₃ : Set G) := fun u hu =>
  mem_normalizer_fintype fun x hx => by
    have hxs : x ∈ d.R ⊔ d.D₂ := h.R₃_le_R_sup_D₂ hx
    have hθ := (h.mem_R₃_iff_of_mem_R_sup_D₂ hxs).1 hx
    have hc : u * x * u⁻¹ ∈ d.R ⊔ d.D₂ :=
      mul_mem (mul_mem (mem_sup_right hu) hxs) (inv_mem (mem_sup_right hu))
    exact (h.mem_R₃_iff_of_mem_R_sup_D₂ hc).2 (h.crossed_conj_mem hu hxs hθ)

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
