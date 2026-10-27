module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S2D
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSFive
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import all CFSG.Fischer.F4

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

@[expose] def Data.M {G : Type} [Group G] (d : Data G) : Subgroup G :=
  d.D₁ ⊓ centralizer ({d.e₂} : Set G)

@[expose] def Data.D₃e₂ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  ⁅d.D₃, zpowers d.e₂⁆

@[expose] def Data.V₃ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  cenMod d.Y d.S₃ ⊓ d.S₃

theorem A₁sub_inf_A₂sub_le {α : SU52} (h1 : α ∈ A₁sub) (h2 : α ∈ A₂sub) :
    α ∈ X₃sub ⊔ X₄sub := by
  rw [← A₁sub_inf_commutator_Ssub]
  exact mem_inf.2 ⟨h1, mem_commutator_Ssub_iff.2
    ⟨A₁sub_le_Ssub h1, (mem_A₁sub.1 h1).2.1, (mem_A₂sub.1 h2).2⟩⟩

open Classical in
@[expose] noncomputable def Data.xi {G : Type} [Group G] (d : Data G) (k : G) : F4 :=
  if h : ∃ α ∈ A₁sub, ∃ w ∈ d.W, d.ι α * w = k then mat (Classical.choose h) 1 0 else 0

theorem e₂_comm_Ssub_mem_A₂sub {σ : SU52} (hσ : σ ∈ Ssub) :
    e₂SU * σ * e₂SU⁻¹ * σ⁻¹ ∈ A₂sub := by
  have hS1 : e₂SU * σ * e₂SU⁻¹ ∈ Ssub := (mem_normalizer_iff.1 e₂SU_mem_normalizer_Ssub σ).1 hσ
  refine mem_A₂sub.2 ⟨mul_mem hS1 (inv_mem hσ), ?_⟩
  rw [mat_mul_one_zero hS1 (inv_mem hσ), mat_conj_e₂ σ 1 0]
  have h2 := mat_mul_one_zero hσ (inv_mem hσ)
  rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide)] at h2
  change F4.ω * mat σ 1 0 * F4.ω⁻¹ + mat σ⁻¹ 1 0 = 0
  rw [mul_comm F4.ω, mul_assoc, mul_inv_cancel₀ (by decide), mul_one]
  exact h2.symm

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem A₁_inf_D₀_le (h : d.Hyp) {a : G} (ha : a ∈ d.A₁) (hD : a ∈ d.D₀) :
    a ∈ d.X₃ ⊔ d.X₄ := by
  rw [h.D₀_eq] at hD
  obtain ⟨b, hb, e, he, hbe⟩ := (h.mem_A₂E₂_iff).1 hD
  have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
  have heL : e ∈ d.L := by
    rw [show e = b⁻¹ * a by rw [hbe]; group]
    exact mul_mem (inv_mem (d.pull_le_L _ hb)) (d.pull_le_L _ ha)
  have heF : e ∈ d.F :=
    (h.mem_F_iff_Y e).2 ⟨heY, mem_centralizer_singleton_iff.1 (h.L_le_H heL)⟩
  have haA₂ : a ∈ d.A₂ := by
    rw [hbe]
    exact mul_mem hb (d.F_le_A₂ heF)
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, hβα⟩ := haA₂
  have e1 : β = α := d.ι_injective hβα
  subst e1
  have h34 := A₁sub_inf_A₂sub_le hα hβ
  have : d.ι β ∈ d.pull (X₃sub ⊔ X₄sub) := ⟨β, h34, rfl⟩
  rwa [d.pull_sup] at this

theorem D₁_inf_D₂_le_D₃ (h : d.Hyp) : d.D₁ ⊓ d.D₂ ≤ d.D₃ := by
  intro x hx
  obtain ⟨hxD₁, hxD₂⟩ := Subgroup.mem_inf.1 hx
  refine h.mem_D₃_of_crossed_mem hxD₁ ?_
  have h1 : x * d.t * x⁻¹ * d.t ∈ d.AW := h.conj_t_mul_t_mem_AW (D₁_le_XW hxD₁)
  have h2 : x * d.t * x⁻¹ * d.t ∈ d.D₀ := h.crossed_mem_D₀ (D₂_le_XC₀ hxD₂)
  obtain ⟨a, ha, w, hw, e⟩ := h.exists_eq_mul_of_mem_AW h1
  have haD : a ∈ d.D₀ := by
    rw [show a = (x * d.t * x⁻¹ * d.t) * w⁻¹ by rw [← e]; group]
    exact mul_mem h2 (inv_mem (Y_le_D₀ (d.W_le_Y hw)))
  rw [← e]
  exact mul_mem (mem_sup_left (h.A₁_inf_D₀_le ha haD)) (mem_sup_right hw)

theorem xi_ι_mul (h : d.Hyp) {α : SU52} (hα : α ∈ A₁sub) {w : G} (hw : w ∈ d.W) :
    d.xi (d.ι α * w) = mat α 1 0 := by
  have hex : ∃ β ∈ A₁sub, ∃ w' ∈ d.W, d.ι β * w' = d.ι α * w := ⟨α, hα, w, hw, rfl⟩
  rw [Data.xi, dif_pos hex]
  obtain ⟨hβ, w', hw', hβw⟩ := Classical.choose_spec hex
  generalize Classical.choose hex = β at hβ hβw ⊢
  have hι : d.ι (α⁻¹ * β) = w * w'⁻¹ := by
    rw [map_mul, map_inv]
    calc (d.ι α)⁻¹ * d.ι β = (d.ι α)⁻¹ * (d.ι β * w' * w'⁻¹) := by group
      _ = (d.ι α)⁻¹ * (d.ι α * w * w'⁻¹) := by rw [hβw]
      _ = w * w'⁻¹ := by group
  have hZ : α⁻¹ * β ∈ ZX₄sub := by
    have : d.ι (α⁻¹ * β) ∈ d.W ⊓ d.H := Subgroup.mem_inf.2
      ⟨hι ▸ mul_mem hw (inv_mem hw'), h.L_le_H (d.ι_mem _)⟩
    rw [h.sec4_9_W.2.1] at this
    exact d.ι_mem_pull_iff.1 this
  have h0 : mat (α⁻¹ * β) 1 0 = 0 :=
    mat_one_zero_of_mem_X₃sub_sup_X₄sub (mem_sup_right (ZX₄sub_le_X₄sub hZ))
  have hS1 : α⁻¹ * β ∈ Ssub := mul_mem (inv_mem (A₁sub_le_Ssub hα)) (A₁sub_le_Ssub hβ)
  have e := mat_mul_one_zero (A₁sub_le_Ssub hα) hS1
  rw [mul_inv_cancel_left, h0, add_zero] at e
  exact e

theorem xi_of_mem_W (h : d.Hyp) {w : G} (hw : w ∈ d.W) : d.xi w = 0 := by
  have := h.xi_ι_mul (one_mem _) hw
  rw [map_one, one_mul] at this
  rw [this, mat_one]
  exact Matrix.one_apply_ne (by decide)

theorem xi_mul (h : d.Hyp) {k k' : G} (hk : k ∈ d.AW) (hk' : k' ∈ d.AW) :
    d.xi (k * k') = d.xi k + d.xi k' := by
  obtain ⟨a, ha, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_AW hk
  obtain ⟨a', ha', w', hw', rfl⟩ := h.exists_eq_mul_of_mem_AW hk'
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨α', hα', rfl⟩ := ha'
  have e : d.ι α * w * (d.ι α' * w') = d.ι (α * α') * (w * w') := by
    have hc : d.ι α' * w = w * d.ι α' := h.A₁_comm_W ⟨α', hα', rfl⟩ hw
    rw [map_mul]
    calc d.ι α * w * (d.ι α' * w') = d.ι α * (w * d.ι α') * w' := by group
      _ = d.ι α * (d.ι α' * w) * w' := by rw [hc]
      _ = d.ι α * d.ι α' * (w * w') := by group
  rw [e, h.xi_ι_mul (mul_mem hα hα') (mul_mem hw hw'), h.xi_ι_mul hα hw, h.xi_ι_mul hα' hw',
    mat_mul_one_zero (A₁sub_le_Ssub hα) (A₁sub_le_Ssub hα')]

theorem xi_one (h : d.Hyp) : d.xi 1 = 0 := h.xi_of_mem_W (one_mem _)

theorem xi_eq_zero_iff (h : d.Hyp) {k : G} (hk : k ∈ d.AW) :
    d.xi k = 0 ↔ k ∈ (d.X₃ ⊔ d.X₄) ⊔ d.W := by
  constructor
  · intro h0
    obtain ⟨a, ha, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_AW hk
    obtain ⟨α, hα, rfl⟩ := ha
    rw [h.xi_ι_mul hα hw] at h0
    have h34 := mem_X₃sub_sup_X₄sub_of_mem_A₁sub hα h0
    have : d.ι α ∈ d.X₃ ⊔ d.X₄ := by
      have : d.ι α ∈ d.pull (X₃sub ⊔ X₄sub) := ⟨α, h34, rfl⟩
      rwa [d.pull_sup] at this
    exact mul_mem (mem_sup_left this) (mem_sup_right hw)
  · intro hk'
    obtain ⟨a, ha, w, hw, e⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha w hw => h.X₃₄_comm_W ha hw) hk'
    have ha' : a ∈ d.pull (X₃sub ⊔ X₄sub) := by
      rw [d.pull_sup]
      exact ha
    obtain ⟨γ, hγ, rfl⟩ := ha'
    rw [← e, h.xi_ι_mul ((sup_le X₃sub_le_A₁sub X₄sub_le_A₁sub') hγ) hw]
    exact mat_one_zero_of_mem_X₃sub_sup_X₄sub hγ

theorem theta_mem_AW (h : d.Hyp) {x : G} (hx : x ∈ d.D₁) : x * d.t * x⁻¹ * d.t ∈ d.AW :=
  h.conj_t_mul_t_mem_AW (D₁_le_XW hx)

theorem xi_theta_mul (h : d.Hyp) {x y : G} (hx : x ∈ d.D₁) (hy : y ∈ d.D₁) :
    d.xi (x * y * d.t * (x * y)⁻¹ * d.t) =
      d.xi (x * d.t * x⁻¹ * d.t) + d.xi (y * d.t * y⁻¹ * d.t) := by
  obtain ⟨w, hw, e⟩ := h.crossed_mul_mem (Subgroup.mem_inf.1 hx).1 (D₁_le_XW hy)
  have hAW : (x * d.t * x⁻¹ * d.t) ∈ d.AW := h.theta_mem_AW hx
  have hAW' : (y * d.t * y⁻¹ * d.t) ∈ d.AW := h.theta_mem_AW hy
  have hw' : w ∈ d.AW := mem_sup_right hw
  rw [e, h.xi_mul (mul_mem hAW' hAW) hw', h.xi_mul hAW' hAW, h.xi_of_mem_W hw, add_zero,
    add_comm]

theorem xi_theta_one (h : d.Hyp) : d.xi ((1 : G) * d.t * (1 : G)⁻¹ * d.t) = 0 := by
  rw [inv_one, one_mul, mul_one, h.t_mul_t]
  exact h.xi_one

theorem xi_theta_inv (h : d.Hyp) {x : G} (hx : x ∈ d.D₁) :
    d.xi (x⁻¹ * d.t * x⁻¹⁻¹ * d.t) = - d.xi (x * d.t * x⁻¹ * d.t) := by
  have := h.xi_theta_mul hx (inv_mem hx)
  rw [mul_inv_cancel] at this
  have h1 := h.xi_theta_one
  rw [this] at h1
  exact eq_neg_of_add_eq_zero_right h1

theorem D₃_le_D₁' : d.D₃ ≤ d.D₁ := fun _ hu => (Subgroup.mem_inf.1 hu).2

theorem mem_D₃_iff_xi (h : d.Hyp) {x : G} (hx : x ∈ d.D₁) :
    x ∈ d.D₃ ↔ d.xi (x * d.t * x⁻¹ * d.t) = 0 := by
  rw [h.xi_eq_zero_iff (h.theta_mem_AW hx)]
  exact ⟨h.crossed_mem_of_mem_D₃, h.mem_D₃_of_crossed_mem hx⟩

theorem conj_mem_D₃_of_mem_D₁ (h : d.Hyp) {x u : G} (hx : x ∈ d.D₁) (hu : u ∈ d.D₃) :
    x * u * x⁻¹ ∈ d.D₃ := by
  have huD : u ∈ d.D₁ := D₃_le_D₁' hu
  have hc : x * u * x⁻¹ ∈ d.D₁ := mul_mem (mul_mem hx huD) (inv_mem hx)
  rw [h.mem_D₃_iff_xi hc]
  have e1 := h.xi_theta_mul hx (mul_mem huD (inv_mem hx))
  have e2 := h.xi_theta_mul huD (inv_mem hx)
  have e3 := h.xi_theta_inv hx
  have e4 := (h.mem_D₃_iff_xi huD).1 hu
  rw [← mul_assoc x u x⁻¹] at e1
  rw [e1, e2, e3, e4]
  ring

theorem xi_conj_e₂ (h : d.Hyp) {k : G} (hk : k ∈ d.AW) :
    d.xi (d.e₂ * k * d.e₂⁻¹) = d.xi k := by
  obtain ⟨a, ha, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_AW hk
  obtain ⟨α, hα, rfl⟩ := ha
  have hα' : e₂SU * α * e₂SU⁻¹ ∈ A₁sub :=
    conj_mem_A₁sub_of_comm_z (comm_of_mem_CzSub e₂SU_mem_CzSub) hα
  have hw' : d.e₂ * w * d.e₂⁻¹ ∈ d.W :=
    (mem_normalizer_iff.1 (h.NHS_le_normalizer_W h.e₂_mem_NHS) w).1 hw
  have e : d.e₂ * (d.ι α * w) * d.e₂⁻¹ =
      d.ι (e₂SU * α * e₂SU⁻¹) * (d.e₂ * w * d.e₂⁻¹) := by
    simp only [Data.e₂, map_mul, map_inv]
    group
  rw [e, h.xi_ι_mul hα' hw', h.xi_ι_mul hα hw, mat_conj_e₂ α 1 0]
  change F4.ω * mat α 1 0 * F4.ω⁻¹ = mat α 1 0
  rw [mul_comm F4.ω, mul_assoc, mul_inv_cancel₀ (by decide), mul_one]

theorem commutator_e₂_mem_D₃ (h : d.Hyp) {x : G} (hx : x ∈ d.D₁) :
    d.e₂ * x * d.e₂⁻¹ * x⁻¹ ∈ d.D₃ := by
  have he := h.NHS_le_XW h.e₂_mem_NHS
  have hy : d.e₂ * x * d.e₂⁻¹ ∈ d.D₁ := h.conj_mem_D₁ he hx
  have hc : d.e₂ * x * d.e₂⁻¹ * x⁻¹ ∈ d.D₁ := mul_mem hy (inv_mem hx)
  rw [h.mem_D₃_iff_xi hc]
  have e1 := h.xi_theta_mul hy (inv_mem hx)
  have e2 := h.xi_theta_inv hx
  have e3 : d.e₂ * x * d.e₂⁻¹ * d.t * (d.e₂ * x * d.e₂⁻¹)⁻¹ * d.t =
      d.e₂ * (x * d.t * x⁻¹ * d.t) * d.e₂⁻¹ :=
    crossed_conj_of_mem_H (Subgroup.mem_inf.1 h.e₂_mem_NHS).2
  rw [e1, e2, e3, h.xi_conj_e₂ (h.theta_mem_AW hx)]
  ring

theorem S_le_normalizer_D₂ (h : d.Hyp) : d.S ≤ normalizer (d.D₂ : Set G) :=
  (h.S_le_NHA₂.trans h.NHA₂_le_XC₀).trans h.XC₀_le_normalizer_D₂

theorem A₂_le_D₂' (h : d.Hyp) : d.A₂ ≤ d.D₂ := by
  rw [← h.D₂_inf_H]
  exact inf_le_left

theorem D₃_le_S₃' (h : d.Hyp) : d.D₃ ≤ d.S₃ := by
  rw [h.S₃_eq]
  exact le_sup_right

theorem exists_eq_mul_of_mem_D₃ (h : d.Hyp) {u : G} (hu : u ∈ d.D₃) :
    ∃ s ∈ d.S, ∃ e ∈ d.D₂, u = s * e := by
  have hset := coe_mul_of_left_le_normalizer_right d.S d.D₂ h.S_le_normalizer_D₂
  have hmem : u ∈ (d.S : Set G) * (d.D₂ : Set G) := by
    rw [← hset]
    exact h.S₃_le_S_sup_D₂ (h.D₃_le_S₃' hu)
  obtain ⟨s, hs, e, he, hse⟩ := hmem
  exact ⟨s, hs, e, he, hse.symm⟩

theorem e₂_comm_D₃_mem_D₂ (h : d.Hyp) {u : G} (hu : u ∈ d.D₃) :
    d.e₂ * u * d.e₂⁻¹ * u⁻¹ ∈ d.D₂ := by
  obtain ⟨s, hs, e, he, rfl⟩ := h.exists_eq_mul_of_mem_D₃ hu
  have hsX : s ∈ d.XC₀ := (h.S_le_NHA₂.trans h.NHA₂_le_XC₀) hs
  have hb : d.e₂ * e * d.e₂⁻¹ ∈ d.D₂ := h.conj_mem_D₂ h.e₂_mem_XC₀ he
  have ha : d.e₂ * s * d.e₂⁻¹ * s⁻¹ ∈ d.A₂ := by
    obtain ⟨σ, hσ, rfl⟩ := hs
    exact ⟨_, e₂_comm_Ssub_mem_A₂sub hσ, by simp only [Data.e₂, map_mul, map_inv]⟩
  have hs' : s * (d.e₂ * e * d.e₂⁻¹ * e⁻¹) * s⁻¹ ∈ d.D₂ :=
    h.conj_mem_D₂ hsX (mul_mem hb (inv_mem he))
  rw [show d.e₂ * (s * e) * d.e₂⁻¹ * (s * e)⁻¹ =
    (d.e₂ * s * d.e₂⁻¹ * s⁻¹) * (s * (d.e₂ * e * d.e₂⁻¹ * e⁻¹) * s⁻¹) by group]
  exact mul_mem (h.A₂_le_D₂' ha) hs'

theorem e₂_mem_cenMod_D₂_D₃ (h : d.Hyp) : d.e₂ ∈ cenMod d.D₂ d.D₃ :=
  ⟨h.XC₀_le_normalizer_D₂ h.e₂_mem_XC₀, fun _ hu => h.e₂_comm_D₃_mem_D₂ hu⟩

theorem isPGroup_zpowers_e₂ (h : d.Hyp) : IsPGroup 3 (zpowers d.e₂) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf d.e₂ = 3 := by
    rw [Data.e₂, orderOf_injective d.ι d.ι_injective, orderOf_e₂SU]
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho]; norm_num)

theorem zpowers_e₂_le_normalizer_D₃ (h : d.Hyp) : zpowers d.e₂ ≤ normalizer (d.D₃ : Set G) :=
  zpowers_le.2 (mem_normalizer_fintype fun _ hu => h.conj_mem_D₃ h.e₂_mem_NHS hu)

theorem D₃e₂_le_D₂ (h : d.Hyp) : d.D₃e₂ ≤ d.D₂ := by
  rw [Data.D₃e₂, Subgroup.commutator_le]
  intro u hu g hg
  have hg' : g ∈ cenMod d.D₂ d.D₃ := (zpowers_le.2 h.e₂_mem_cenMod_D₂_D₃) hg
  rw [commutatorElement_def, show u * g * u⁻¹ * g⁻¹ = (g * u * g⁻¹ * u⁻¹)⁻¹ by group]
  exact inv_mem (hg'.2 u hu)

theorem D₃e₂_le_D₃ (h : d.Hyp) : d.D₃e₂ ≤ d.D₃ :=
  CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing d.D₃ (zpowers d.e₂)
    h.zpowers_e₂_le_normalizer_D₃

theorem M_le_D₁ : d.M ≤ d.D₁ := inf_le_left

theorem D₃_inf_centralizer_le_M (h : d.Hyp) :
    d.D₃ ⊓ centralizer ((zpowers d.e₂ : Subgroup G) : Set G) ≤ d.M :=
  inf_le_inf D₃_le_D₁' (centralizer_le (Set.singleton_subset_iff.2 (mem_zpowers _)))

theorem exists_eq_mul_of_mem_D₁ (h : d.Hyp) {x : G} (hx : x ∈ d.D₁) :
    ∃ u ∈ d.D₃, ∃ m ∈ d.M, x = u * m := by
  let T : Set G := (fun u => x * u) '' (d.D₃ : Set G)
  have hT : ∀ y ∈ T, d.e₂ * y * d.e₂⁻¹ ∈ T := by
    rintro _ ⟨u, hu, rfl⟩
    have hc := h.commutator_e₂_mem_D₃ hx
    have hu' : d.e₂ * u * d.e₂⁻¹ ∈ d.D₃ := h.conj_mem_D₃ h.e₂_mem_NHS hu
    refine ⟨(x⁻¹ * (d.e₂ * x * d.e₂⁻¹ * x⁻¹) * x) * (d.e₂ * u * d.e₂⁻¹), mul_mem ?_ hu', ?_⟩
    · have := h.conj_mem_D₃_of_mem_D₁ (inv_mem hx) hc
      rwa [inv_inv] at this
    · group
  have hcard : T.ncard = 2 ^ 12 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective x), ← Nat.card_coe_set_eq]
    exact h.card_D₃
  obtain ⟨_, ⟨u, hu, rfl⟩, hfix⟩ :=
    exists_conj_fixed (e₂_pow_three (d := d)) hT (by rw [hcard]; norm_num)
  have hy : x * u ∈ d.M := Subgroup.mem_inf.2 ⟨mul_mem hx (D₃_le_D₁' hu),
    mem_centralizer_singleton_iff.2 (by
      calc x * u * d.e₂ = d.e₂ * (x * u) * d.e₂⁻¹ * d.e₂ := by rw [hfix]
        _ = d.e₂ * (x * u) := by group)⟩
  refine ⟨(x * u) * u⁻¹ * (x * u)⁻¹, ?_, x * u, hy, by group⟩
  exact h.conj_mem_D₃_of_mem_D₁ (M_le_D₁ hy) (inv_mem hu)

theorem D₁_eq_D₃e₂_sup_M (h : d.Hyp) : d.D₁ = d.D₃e₂ ⊔ d.M := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, m, hm, rfl⟩ := h.exists_eq_mul_of_mem_D₁ hx
    have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
      Nat.prime_three (zpowers d.e₂) d.D₃ h.isPGroup_zpowers_e₂ h.zpowers_e₂_le_normalizer_D₃
      (by rw [h.card_D₃]; norm_num)
    have hu' : u ∈ d.D₃e₂ ⊔ d.M :=
      (sup_le_sup_left h.D₃_inf_centralizer_le_M _) (hfac.symm.le hu)
    exact mul_mem hu' (mem_sup_right hm)
  · exact sup_le (h.D₃e₂_le_D₃.trans D₃_le_D₁') M_le_D₁

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
