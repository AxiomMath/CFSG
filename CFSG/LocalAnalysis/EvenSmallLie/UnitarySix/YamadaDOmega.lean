module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDV2

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem conj_image_smul {V : Subgroup G} {x : G} (hx : x ∈ normalizer (V : Set G)) (y : G) :
    (fun g => x * g * x⁻¹) '' (y • (V : Set G)) = (x * y * x⁻¹) • (V : Set G) := by
  ext g
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨x * v * x⁻¹, (mem_normalizer_iff.mp hx v).mp hv, ?_⟩
    simp only [smul_eq_mul]
    group
  · rintro ⟨v, hv, rfl⟩
    have hv' : x⁻¹ * v * x ∈ V := by
      have := (mem_normalizer_iff.mp (inv_mem hx) v).mp hv
      rwa [inv_inv] at this
    refine ⟨y * (x⁻¹ * v * x), ⟨x⁻¹ * v * x, hv', rfl⟩, ?_⟩
    simp only [smul_eq_mul]
    group

namespace Data

variable (d : Data G)

abbrev XV : Subgroup G := normalizer (d.C₀ : Set G) ⊓ normalizer (d.V₁ : Set G)

@[expose] def Om : Set (Set G) := {S | ∃ x ∈ d.XV, S = (x * d.t * x⁻¹) • (d.V₁ : Set G)}

@[expose] def Cyc : Prop := ∃ v ∈ d.V₁, v * v ≠ 1

abbrev XS : Subgroup G := d.XV ⊓ normalizer (d.E₈ : Set G)

theorem conj_mem_Om {x : G} (hx : x ∈ d.XV) {S : Set G} (hS : S ∈ d.Om) :
    (fun g => x * g * x⁻¹) '' S ∈ d.Om := by
  obtain ⟨y, hy, rfl⟩ := hS
  refine ⟨x * y, mul_mem hx hy, ?_⟩
  rw [conj_image_smul (mem_inf.mp hx).2]
  congr 1
  group

theorem tV_mem_Om : d.t • (d.V₁ : Set G) ∈ d.Om :=
  ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩

@[expose] def omegaConj (x : d.XV) : Equiv.Perm d.Om where
  toFun S := ⟨(fun g => (x : G) * g * (x : G)⁻¹) '' S, d.conj_mem_Om x.2 S.2⟩
  invFun S := ⟨(fun g => (x : G)⁻¹ * g * (x : G)⁻¹⁻¹) '' S, d.conj_mem_Om (inv_mem x.2) S.2⟩
  left_inv S := Subtype.ext (by simp [Set.image_image, mul_assoc])
  right_inv S := Subtype.ext (by simp [Set.image_image, mul_assoc])

@[expose] def omegaPerm : d.XV →* Equiv.Perm d.Om where
  toFun := d.omegaConj
  map_one' := Equiv.ext fun S => Subtype.ext (by simp [omegaConj])
  map_mul' x y := Equiv.ext fun S => Subtype.ext (by
    simp [omegaConj, Set.image_image, mul_assoc])

theorem omegaPerm_apply (x : d.XV) (S : d.Om) :
    ((d.omegaPerm x S : d.Om) : Set G) = (fun g => (x : G) * g * (x : G)⁻¹) '' S := rfl

end Data

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem K₁_le_X [Finite G] : d.K₁ ≤ normalizer (d.ZR : Set G) := fun _ hk =>
  CHz_le_X (mem_inf.mpr ⟨h.K₁_cent_z hk, h.L_le_H (h.K₁_le_L hk)⟩)

theorem X_le_XV [Finite G] : normalizer (d.ZR : Set G) ≤ d.XV :=
  le_inf X_le_normalizer_C₀ h.X_le_normalizer_V₁

theorem K₁_le_XV [Finite G] : d.K₁ ≤ d.XV := h.K₁_le_X.trans h.X_le_XV

theorem C₀_le_XV [Finite G] : d.C₀ ≤ d.XV := (oTwo_le _).trans h.X_le_XV

theorem V₂_le_XV [Finite G] : d.V₂ ≤ d.XV := le_inf h.V₂_le_normalizer_C₀ h.V₂_le_normalizer_V₁

theorem t_mem_C₀ [Finite G] : d.t ∈ d.C₀ := by
  rw [h.C₀_eq]
  exact mem_sup_right (mem_sup_right (mem_zpowers _))

theorem coset_eq_iff [Finite G] {a b : G} (ha : a ∈ d.A₁) (hb : b ∈ d.A₁) :
    (a * d.t) • (d.V₁ : Set G) = (b * d.t) • (d.V₁ : Set G) ↔ a⁻¹ * b ∈ zpowers d.z := by
  have hab : a⁻¹ * b ∈ d.L := h.A₁_le_L (mul_mem (inv_mem ha) hb)
  have hc : (a * d.t)⁻¹ * (b * d.t) = a⁻¹ * b := by
    calc (a * d.t)⁻¹ * (b * d.t) = d.t⁻¹ * ((a⁻¹ * b) * d.t) := by group
      _ = d.t⁻¹ * (d.t * (a⁻¹ * b)) := by rw [h.comm_of_mem_L hab]
      _ = a⁻¹ * b := by group
  rw [leftCoset_eq_iff, hc]
  constructor
  · intro hV
    exact h.V₁_inf_H_le (mem_inf.mpr ⟨hV, h.L_le_H hab⟩)
  · intro hz
    exact (zpowers_le.mpr h.z_mem_V₁) hz

theorem not_mem_zpowers_z_of_sq_ne {v : G} (hv : v * v ≠ 1) : v ∉ zpowers d.z := by
  intro hvz
  rcases h.mem_zpowers_z_iff.mp hvz with rfl | rfl
  · exact hv (mul_one 1)
  · exact hv h.z_sq

theorem sq_eq_z_of_cyc [Finite G] (hc : d.Cyc) {w : G} (hw : w ∈ d.V₁)
    (hwz : w ∉ zpowers d.z) : w * w = d.z := by
  obtain ⟨v, hv, hv1⟩ := hc
  have hvz := h.not_mem_zpowers_z_of_sq_ne hv1
  have hU : ∀ {y}, y ∈ d.V₁ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.V₁_le_D hy)
  have hvvH : v * v ∈ d.H := by
    have hcr : (v * v)⁻¹ * d.t * (v * v) * d.t = 1 := by
      rw [h.crossed_U₄_mul (hU hv) (hU hv), h.crossed_V₁_eq_z hv hvz, h.z_sq]
    exact mem_centralizer_singleton_iff.mpr ((crossed_eq_one_iff h.t_sq).mp hcr)
  have hvv : v * v = d.z := by
    rcases h.mem_zpowers_z_iff.mp (h.V₁_inf_H_le (mem_inf.mpr ⟨mul_mem hv hv, hvvH⟩)) with
      h1 | h1
    · exact absurd h1 hv1
    · exact h1
  have hwv := h.mul_inv_mem_zpowers_z hv hw hvz hwz
  have hc2 : (w * v⁻¹) * (w * v⁻¹) = 1 := by
    rcases h.mem_zpowers_z_iff.mp hwv with h1 | h1
    · rw [h1, mul_one]
    · rw [h1, h.z_sq]
  have hcomm : (w * v⁻¹) * v = v * (w * v⁻¹) :=
    h.V₁_comm (mul_mem hw (inv_mem hv)) hv
  calc w * w = ((w * v⁻¹) * v) * ((w * v⁻¹) * v) := by group
    _ = ((w * v⁻¹) * (w * v⁻¹)) * (v * v) := by
      rw [show ((w * v⁻¹) * v) * ((w * v⁻¹) * v) = (w * v⁻¹) * (v * (w * v⁻¹)) * v by group,
        ← hcomm]
      group
    _ = d.z := by rw [hc2, hvv, one_mul]

theorem wt_sq_of_cyc [Finite G] (hc : d.Cyc) {w : G} (hw : w ∈ d.V₁) :
    (w * d.t) * (w * d.t) = 1 := by
  by_cases hwz : w ∈ zpowers d.z
  · have hwt : w * d.t = d.t * w := by
      rcases h.mem_zpowers_z_iff.mp hwz with rfl | rfl
      · group
      · exact h.z_comm_t
    have hww : w * w = 1 := by
      rcases h.mem_zpowers_z_iff.mp hwz with rfl | rfl
      · group
      · exact h.z_sq
    calc (w * d.t) * (w * d.t) = w * (d.t * w) * d.t := by group
      _ = (w * w) * (d.t * d.t) := by rw [← hwt]; group
      _ = 1 := by rw [hww, h.t_sq, one_mul]
  · have hcr := h.crossed_V₁_eq_z hw hwz
    have htw : d.t * w * d.t = w * d.z := by
      rw [← hcr]
      group
    calc (w * d.t) * (w * d.t) = w * (d.t * w * d.t) := by group
      _ = (w * w) * d.z := by rw [htw]; group
      _ = 1 := by rw [h.sq_eq_z_of_cyc hc hw hwz, h.z_sq]

theorem cent_z_of_cyc [Finite G] (hc : d.Cyc) {x : G} (hx : x ∈ normalizer (d.V₁ : Set G)) :
    x * d.z = d.z * x := by
  obtain ⟨v, hv, hv1⟩ := hc
  have hvz := h.not_mem_zpowers_z_of_sq_ne hv1
  have hvv := h.sq_eq_z_of_cyc ⟨v, hv, hv1⟩ hv hvz
  have hxv : x * v * x⁻¹ ∈ d.V₁ := (mem_normalizer_iff.mp hx v).mp hv
  have hsq : (x * v * x⁻¹) * (x * v * x⁻¹) = x * d.z * x⁻¹ := by
    rw [← hvv]
    group
  have hxvz : x * v * x⁻¹ ∉ zpowers d.z := by
    refine h.not_mem_zpowers_z_of_sq_ne ?_
    rw [hsq]
    intro h1
    apply h.z_ne_one
    calc d.z = x⁻¹ * (x * d.z * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  have e := h.sq_eq_z_of_cyc ⟨v, hv, hv1⟩ hxv hxvz
  rw [hsq] at e
  calc x * d.z = x * d.z * x⁻¹ * x := by group
    _ = d.z * x := by rw [e]

theorem exists_of_mem_C₀ [Finite G] {y : G} (hy : y ∈ d.C₀)
    (hyV : y ∉ centralizer (d.V₁ : Set G)) : ∃ a ∈ d.A₁, ∃ w ∈ d.V₁, y = a * w * d.t := by
  rw [h.C₀_eq] at hy
  obtain ⟨a, ha, e, he, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha e he => (mem_centralizer_iff.mp (h.E₈_le_cent_A₁ he) a ha)) hy
  rcases h.mem_E₈_iff.mp he with heV | heV
  · exfalso
    apply hyV
    rw [mem_centralizer_iff]
    intro v hv
    have hav : v * a = a * v := (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) a ha).symm
    calc v * (a * e) = a * (v * e) := by rw [← mul_assoc, hav, mul_assoc]
      _ = a * e * v := by rw [h.V₁_comm hv heV, mul_assoc]
  · refine ⟨a, ha, e * d.t⁻¹, heV, ?_⟩
    group

theorem t_not_cent_V₁ [Finite G] : d.t ∉ centralizer (d.V₁ : Set G) := by
  intro ht
  obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
  have e : v * d.t = d.t * v := (mem_centralizer_iff.mp ht v hv)
  apply h.z_ne_one
  have : v⁻¹ * d.t * v = d.t := by rw [mul_assoc, ← e]; group
  rw [this] at hvt
  calc d.z = d.z * d.t * d.t⁻¹ := by group
    _ = 1 := by rw [← hvt]; group

theorem Om_subset_of_cyc [Finite G] (hc : d.Cyc) {S : Set G} (hS : S ∈ d.Om) :
    ∃ a ∈ d.A₁, a * a = 1 ∧ S = (a * d.t) • (d.V₁ : Set G) := by
  obtain ⟨x, hx, rfl⟩ := hS
  obtain ⟨hxC, hxV⟩ := mem_inf.mp hx
  have hyC : x * d.t * x⁻¹ ∈ d.C₀ := (mem_normalizer_iff.mp hxC d.t).mp h.t_mem_C₀
  have hyV : x * d.t * x⁻¹ ∉ centralizer (d.V₁ : Set G) := by
    intro hy
    apply h.t_not_cent_V₁
    rw [mem_centralizer_iff]
    intro v hv
    have hv' : x * v * x⁻¹ ∈ d.V₁ := (mem_normalizer_iff.mp hxV v).mp hv
    have e := mem_centralizer_iff.mp hy _ hv'
    calc v * d.t = x⁻¹ * ((x * v * x⁻¹) * (x * d.t * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * d.t * x⁻¹) * (x * v * x⁻¹)) * x := by rw [e]
      _ = d.t * v := by group
  obtain ⟨a, ha, w, hw, hy⟩ := h.exists_of_mem_C₀ hyC hyV
  have hat : a * d.t = d.t * a := h.comm_of_mem_L (h.A₁_le_L ha)
  have haw : a * w = w * a := mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha
  have hyy : (x * d.t * x⁻¹) * (x * d.t * x⁻¹) = 1 := by
    rw [show (x * d.t * x⁻¹) * (x * d.t * x⁻¹) = x * (d.t * d.t) * x⁻¹ by group, h.t_sq]
    group
  have haa : a * a = 1 := by
    have e : (a * w * d.t) * (a * w * d.t) = (a * a) * ((w * d.t) * (w * d.t)) := by
      calc (a * w * d.t) * (a * w * d.t) = a * w * (d.t * a) * w * d.t := by group
        _ = a * (w * a) * d.t * w * d.t := by rw [← hat]; group
        _ = (a * a) * ((w * d.t) * (w * d.t)) := by rw [← haw]; group
    calc a * a = (a * a) * ((w * d.t) * (w * d.t)) := by rw [h.wt_sq_of_cyc hc hw, mul_one]
      _ = (a * w * d.t) * (a * w * d.t) := e.symm
      _ = 1 := by rw [← hy, hyy]
  refine ⟨a, ha, haa, ?_⟩
  rw [hy, leftCoset_eq_iff]
  have htw : d.t⁻¹ * w⁻¹ * d.t ∈ d.V₁ := by
    have := (mem_normalizer_iff.mp (inv_mem h.t_mem_normalizer_V₁) w⁻¹).mp (inv_mem hw)
    rwa [inv_inv] at this
  rw [show (a * w * d.t)⁻¹ * (a * d.t) = d.t⁻¹ * w⁻¹ * d.t by group]
  exact htw

theorem exists_b₀ [Finite G] : ∃ b ∈ d.X₈, b * b = 1 ∧ b ∉ zpowers d.z := by
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ d.X₈, b ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : d.X₈ = ⊥ := eq_bot_iff.mpr fun b hb => mem_bot.mpr (hne b hb)
    have := h.card_X₈
    rw [hbot, card_bot] at this
    exact absurd this (by norm_num)
  refine ⟨b, hb, h.A₄_sq (h.X₈_le_A₄ hb), fun hbz => hb1 ?_⟩
  have : b ∈ d.X₈ ⊓ zpowers d.z := mem_inf.mpr ⟨hb, hbz⟩
  rwa [h.X₈_inf_z, mem_bot] at this

theorem coset_mem_Om [Finite G] {a : G} (ha : a ∈ d.A₁) (ha2 : a * a = 1) :
    (a * d.t) • (d.V₁ : Set G) ∈ d.Om := by
  by_cases haz : a ∈ zpowers d.z
  · refine ⟨1, one_mem _, ?_⟩
    rw [show (1 : G) * d.t * 1⁻¹ = 1 * d.t by group, h.coset_eq_iff ha (one_mem _)]
    simpa using haz
  obtain ⟨b, hb, hb2, hbz⟩ := h.exists_b₀
  have hbA := h.X₈_le_A₁ hb
  obtain ⟨k, hk, hka⟩ := h.K₁_trans b hbA hb2 hbz a ha ha2 haz
  obtain ⟨y, hy, hyt⟩ := h.exists_V₂_conj (mem_sup_left hb : b ∈ d.Z₂S)
  have hkt : k * d.t = d.t * k := h.comm_of_mem_L (h.K₁_le_L hk)
  have hkt' : d.t * k⁻¹ = k⁻¹ * d.t := (Commute.inv_left (show Commute k d.t from hkt)).symm
  have hkbA : k * b * k⁻¹ ∈ d.A₁ :=
    (mem_normalizer_iff.mp (h.CHz_le (mem_inf.mpr ⟨h.K₁_cent_z hk,
      h.L_le_H (h.K₁_le_L hk)⟩)) b).mp hbA
  refine ⟨k * y⁻¹, mul_mem (h.K₁_le_XV hk) (inv_mem (h.V₂_le_XV hy)), ?_⟩
  have e : k * y⁻¹ * d.t * (k * y⁻¹)⁻¹ = (k * b * k⁻¹) * d.t := by
    have hyt' : y⁻¹ * d.t * y = b * d.t := by
      rw [← hyt, mul_assoc _ d.t d.t, h.t_sq, mul_one]
    calc k * y⁻¹ * d.t * (k * y⁻¹)⁻¹ = k * (y⁻¹ * d.t * y) * k⁻¹ := by group
      _ = k * b * (d.t * k⁻¹) := by rw [hyt']; group
      _ = k * b * (k⁻¹ * d.t) := by rw [hkt']
      _ = (k * b * k⁻¹) * d.t := by group
  rw [e, h.coset_eq_iff ha hkbA, show a⁻¹ * (k * b * k⁻¹) = ((k * b * k⁻¹)⁻¹ * a)⁻¹ by group]
  exact inv_mem hka

theorem ncard_Om [Finite G] (hc : d.Cyc) : d.Om.ncard = 136 := by
  rw [← h.card_sing]
  symm
  refine Set.ncard_congr (fun S (hS : ∃ a ∈ d.A₁, a * a = 1 ∧ S = a • (zpowers d.z : Set G)) =>
    (Classical.choose hS * d.t) • (d.V₁ : Set G)) ?_ ?_ ?_
  · intro S hS
    obtain ⟨ha, ha2, -⟩ := Classical.choose_spec hS
    exact h.coset_mem_Om ha ha2
  · intro S S' hS hS' e
    obtain ⟨ha, -, hSa⟩ := Classical.choose_spec hS
    obtain ⟨ha', -, hSa'⟩ := Classical.choose_spec hS'
    rw [hSa, hSa', leftCoset_eq_iff]
    exact (h.coset_eq_iff ha ha').mp e
  · intro T hT
    obtain ⟨a, ha, ha2, rfl⟩ := h.Om_subset_of_cyc hc hT
    have hS : ∃ b ∈ d.A₁, b * b = 1 ∧ a • (zpowers d.z : Set G) = b • (zpowers d.z : Set G) :=
      ⟨a, ha, ha2, rfl⟩
    refine ⟨_, hS, ?_⟩
    obtain ⟨ha', -, e⟩ := Classical.choose_spec hS
    rw [leftCoset_eq_iff] at e
    exact (h.coset_eq_iff ha' ha).mpr (by simpa using inv_mem e)

theorem E₈_comm [Finite G] {e f : G} (he : e ∈ d.E₈) (hf : f ∈ d.E₈) :
    e * f * e⁻¹ * f⁻¹ ∈ d.V₁ := by
  have htV := h.t_mem_normalizer_V₁
  have hN : d.E₈ ≤ normalizer (d.V₁ : Set G) :=
    sup_le (fun _ hv => le_normalizer hv) (zpowers_le.mpr htV)
  have hle : d.E₈ ≤ actTriv d.E₈ d.V₁ := by
    refine sup_le (fun v hv => ⟨le_normalizer (mem_sup_left hv), le_normalizer hv,
      fun c hc => ?_⟩) (zpowers_le.mpr ⟨le_normalizer (mem_sup_right (mem_zpowers _)), htV,
      fun c hc => ?_⟩)
    · have : c * v⁻¹ * c⁻¹ ∈ d.V₁ := (mem_normalizer_iff.mp (hN hc) _).mp (inv_mem hv)
      rw [show v * c * v⁻¹ * c⁻¹ = v * (c * v⁻¹ * c⁻¹) by group]
      exact mul_mem hv this
    · rcases h.mem_E₈_iff.mp hc with hcV | hcV
      · exact mul_mem ((mem_normalizer_iff.mp htV c).mp hcV) (inv_mem hcV)
      · obtain ⟨w, hw, rfl⟩ : ∃ w ∈ d.V₁, c = w * d.t := ⟨c * d.t⁻¹, hcV, by group⟩
        rw [show d.t * (w * d.t) * d.t⁻¹ * (w * d.t)⁻¹ = (d.t * w * d.t⁻¹) * w⁻¹ by group]
        exact mul_mem ((mem_normalizer_iff.mp htV w).mp hw) (inv_mem hw)
  exact (hle he).2.2 f hf

theorem C₀_comm [Finite G] {c y : G} (hc : c ∈ d.C₀) (hy : y ∈ d.C₀) :
    c * y * c⁻¹ * y⁻¹ ∈ d.V₁ := by
  have hNV : d.C₀ ≤ normalizer (d.V₁ : Set G) := fun _ hx => (mem_inf.mp (h.C₀_le_XV hx)).2
  have hcomm : ∀ a ∈ d.A₁, ∀ e ∈ d.E₈, a * e = e * a := fun a ha e he =>
    mem_centralizer_iff.mp (h.E₈_le_cent_A₁ he) a ha
  have hle : d.C₀ ≤ actTriv d.C₀ d.V₁ := by
    rw [h.C₀_eq] at hNV ⊢
    refine sup_le (fun a ha => ⟨le_normalizer (mem_sup_left ha), hNV (mem_sup_left ha),
      fun c hc => ?_⟩) (fun e he => ⟨le_normalizer (mem_sup_right he), hNV (mem_sup_right he),
      fun c hc => ?_⟩)
    · obtain ⟨b, hb, f, hf, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hc
      have hfa : f * a⁻¹ = a⁻¹ * f :=
        (Commute.inv_left (show Commute a f from hcomm a ha f hf)).symm
      have e : a * (b * f) * a⁻¹ * (b * f)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
        calc a * (b * f) * a⁻¹ * (b * f)⁻¹ = a * b * (f * a⁻¹) * f⁻¹ * b⁻¹ := by group
          _ = a * b * (a⁻¹ * f) * f⁻¹ * b⁻¹ := by rw [hfa]
          _ = a * b * a⁻¹ * b⁻¹ := by group
      rw [e]
      exact (zpowers_le.mpr h.z_mem_V₁) (h.A₁_comm a ha b hb)
    · obtain ⟨b, hb, f, hf, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hc
      have e : e * (b * f) * e⁻¹ * (b * f)⁻¹ = b * (e * f * e⁻¹ * f⁻¹) * b⁻¹ := by
        calc e * (b * f) * e⁻¹ * (b * f)⁻¹ = (e * b) * f * e⁻¹ * f⁻¹ * b⁻¹ := by group
          _ = (b * e) * f * e⁻¹ * f⁻¹ * b⁻¹ := by rw [hcomm b hb e he]
          _ = b * (e * f * e⁻¹ * f⁻¹) * b⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.mp (hNV (mem_sup_left hb)) _).mp (h.E₈_comm he hf)
  exact (hle hc).2.2 y hy

theorem omegaPerm_eq_one [Finite G] (x : d.XV) (hx : (x : G) ∈ d.C₀) : d.omegaPerm x = 1 := by
  refine Equiv.ext fun S => Subtype.ext ?_
  obtain ⟨y, hy, hS⟩ := S.2
  have huC : y * d.t * y⁻¹ ∈ d.C₀ := (mem_normalizer_iff.mp (mem_inf.mp hy).1 _).mp h.t_mem_C₀
  rw [Data.omegaPerm_apply, Equiv.Perm.one_apply, hS, conj_image_smul (mem_inf.mp x.2).2,
    leftCoset_eq_iff]
  rw [show ((x : G) * (y * d.t * y⁻¹) * (x : G)⁻¹)⁻¹ * (y * d.t * y⁻¹) =
    (x : G) * (y * d.t * y⁻¹)⁻¹ * (x : G)⁻¹ * (y * d.t * y⁻¹)⁻¹⁻¹ by group]
  exact h.C₀_comm hx (inv_mem huC)

omit h in
theorem mem_X_of [Finite G] {y : G} (hyz : y * d.z = d.z * y) (hyt : y * d.t * y⁻¹ ∈ d.ZR) :
    y ∈ normalizer (d.ZR : Set G) := by
  apply mem_normalizer_of_conj_mem
  have hle : d.ZR ≤ d.ZR.comap (MulAut.conj y).toMonoidHom := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      change y * d.z * y⁻¹ ∈ d.ZR
      rw [hyz, mul_inv_cancel_right]
      exact mem_sup_left (mem_zpowers _)
    · rw [zpowers_le]
      exact hyt
  exact fun b hb => hle hb

theorem conj_t_of_mem_XS [Finite G] {x : G} (hx : x ∈ d.XS) :
    x * d.t * x⁻¹ * d.t⁻¹ ∈ d.V₁ := by
  obtain ⟨hxX, hxE⟩ := mem_inf.mp hx
  have hE : x * d.t * x⁻¹ ∈ d.E₈ :=
    (mem_normalizer_iff.mp hxE d.t).mp (mem_sup_right (mem_zpowers _))
  rcases h.mem_E₈_iff.mp hE with hV | hV
  · exfalso
    apply h.t_not_mem_V₁
    have := (mem_normalizer_iff.mp (inv_mem (mem_inf.mp hxX).2) _).mp hV
    rwa [show x⁻¹ * (x * d.t * x⁻¹) * x⁻¹⁻¹ = d.t by group] at this
  · exact hV

theorem mem_XS_iff [Finite G] {x : G} (hx : x ∈ d.XV) :
    x ∈ d.XS ↔ (x * d.t * x⁻¹) • (d.V₁ : Set G) = d.t • (d.V₁ : Set G) := by
  rw [leftCoset_eq_iff]
  constructor
  · intro hxS
    have := (mem_normalizer_iff.mp (inv_mem h.t_mem_normalizer_V₁) _).mp
      (inv_mem (h.conj_t_of_mem_XS hxS))
    rwa [show d.t⁻¹ * (x * d.t * x⁻¹ * d.t⁻¹)⁻¹ * d.t⁻¹⁻¹ = (x * d.t * x⁻¹)⁻¹ * d.t by group]
      at this
  · intro hV
    refine mem_inf.mpr ⟨hx, mem_normalizer_of_conj_mem fun e he => ?_⟩
    have hxV := (mem_inf.mp hx).2
    rcases h.mem_E₈_iff.mp he with heV | heV
    · exact mem_sup_left ((mem_normalizer_iff.mp hxV e).mp heV)
    · obtain ⟨w, hw, rfl⟩ : ∃ w ∈ d.V₁, e = w * d.t := ⟨e * d.t⁻¹, heV, by group⟩
      have h1 : x * w * x⁻¹ ∈ d.V₁ := (mem_normalizer_iff.mp hxV w).mp hw
      have hu : d.t * ((x * d.t * x⁻¹)⁻¹ * d.t)⁻¹ * d.t⁻¹ ∈ d.V₁ :=
        (mem_normalizer_iff.mp h.t_mem_normalizer_V₁ _).mp (inv_mem hV)
      rw [show d.t * ((x * d.t * x⁻¹)⁻¹ * d.t)⁻¹ * d.t⁻¹ = x * d.t * x⁻¹ * d.t⁻¹ by group] at hu
      refine h.mem_E₈_iff.mpr (Or.inr ?_)
      rw [show x * (w * d.t) * x⁻¹ * d.t⁻¹ = (x * w * x⁻¹) * (x * d.t * x⁻¹ * d.t⁻¹) by group]
      exact mul_mem h1 hu

theorem card_XV_eq [Finite G] : Nat.card d.XV = Nat.card d.Om * Nat.card d.XS := by
  let : MulAction d.XV d.Om := MulAction.compHom _ d.omegaPerm
  have hstab : MulAction.stabilizer d.XV (⟨_, d.tV_mem_Om⟩ : d.Om) = d.XS.subgroupOf d.XV := by
    ext x
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, h.mem_XS_iff x.2, Subtype.ext_iff]
    change (fun g => (x : G) * g * (x : G)⁻¹) '' (d.t • (d.V₁ : Set G)) = _ ↔ _
    rw [conj_image_smul (mem_inf.mp x.2).2]
  have horb : MulAction.orbit d.XV (⟨_, d.tV_mem_Om⟩ : d.Om) = Set.univ := by
    refine Set.eq_univ_of_forall fun S => ?_
    obtain ⟨y, hy, hS⟩ := S.2
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change (fun g => y * g * y⁻¹) '' (d.t • (d.V₁ : Set G)) = S
    rw [conj_image_smul (mem_inf.mp hy).2, hS]
  have hidx := MulAction.index_stabilizer (G := d.XV) (⟨_, d.tV_mem_Om⟩ : d.Om)
  rw [horb, Set.ncard_univ, hstab] at hidx
  rw [← (d.XS.subgroupOf d.XV).card_mul_index, hidx, mul_comm]
  congr 1
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv

theorem X_le_cent_zpowers_z [Finite G] :
    normalizer (d.ZR : Set G) ≤ centralizer ((zpowers d.z : Subgroup G) : Set G) :=
  fun _ hx => mem_centralizer_iff.mpr fun _ hw => (h.X_comm_zpowers_z hx hw).symm

theorem crossed_X [Finite G] {x : G} (hx : x ∈ normalizer (d.ZR : Set G)) :
    x⁻¹ * d.t * x * d.t ∈ zpowers d.z := by
  rcases h.conj_t_of_mem_X hx with e | e <;> rw [e]
  · rw [h.t_sq]
    exact one_mem _
  · rw [mul_assoc, h.t_sq, mul_one]
    exact mem_zpowers _

theorem onto_zpowers_z [Finite G] {Y : Subgroup G} (hY : d.V₁ ≤ Y) {b : G}
    (hb : b ∈ zpowers d.z) : ∃ y ∈ Y, y⁻¹ * d.t * y * d.t = b := by
  rcases h.mem_zpowers_z_iff.mp hb with rfl | rfl
  · exact ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.t_sq]⟩
  · obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
    exact ⟨v, hY hv, by rw [hvt, mul_assoc, h.t_sq, mul_one]⟩

theorem card_X [Finite G] : Nat.card (normalizer (d.ZR : Set G)) =
    Nat.card (centralizer ({d.z} : Set G) ⊓ d.H : Subgroup G) * 2 := by
  rw [card_eq_of_crossed_onto h.t_sq h.X_le_cent_zpowers_z (fun _ hx => h.crossed_X hx)
    (fun _ hb => h.onto_zpowers_z (fun _ hv => h.V₁_le_normalizer_ZR hv) hb), h.card_zpowers_z]
  change Nat.card (normalizer (d.ZR : Set G) ⊓ d.H : Subgroup G) * 2 = _
  rw [h.X_inf_H]

theorem card_C₀ [Finite G] : Nat.card d.C₀ = 2 ^ 11 := by
  have hle : d.C₀ ≤ normalizer (d.ZR : Set G) := oTwo_le _
  have hV : d.V₁ ≤ d.C₀ := by
    rw [h.C₀_eq]
    exact le_sup_right.trans' le_sup_left
  rw [card_eq_of_crossed_onto h.t_sq (hle.trans h.X_le_cent_zpowers_z)
    (fun _ hx => h.crossed_X (hle hx)) (fun _ hb => h.onto_zpowers_z hV hb), h.card_zpowers_z]
  change Nat.card (d.C₀ ⊓ d.H : Subgroup G) * 2 = _
  rw [h.C₀_inf_H, h.card_withT h.A₁_le_L, h.card_A₁]
  norm_num

theorem conj_t_not_mem_of_cyc [Finite G] (hc : d.Cyc) {x : G} (hx : x ∈ d.XS)
    (hxN : x ∉ normalizer (d.ZR : Set G)) : x * d.t * x⁻¹ * d.t⁻¹ ∉ zpowers d.z := by
  intro hz
  apply hxN
  refine mem_X_of (h.cent_z_of_cyc hc (mem_inf.mp (mem_inf.mp hx).1).2) ?_
  rw [show x * d.t * x⁻¹ = (x * d.t * x⁻¹ * d.t⁻¹) * d.t by group]
  exact mul_mem (mem_sup_left hz) (mem_sup_right (mem_zpowers _))

theorem mul_mem_X_of_cyc [Finite G] (hc : d.Cyc) {x x' : G} (hx : x ∈ d.XS) (hx' : x' ∈ d.XS)
    (hxN : x ∉ normalizer (d.ZR : Set G)) (hx'N : x' ∉ normalizer (d.ZR : Set G)) :
    x⁻¹ * x' ∈ normalizer (d.ZR : Set G) := by
  have hxz := h.cent_z_of_cyc hc (mem_inf.mp (mem_inf.mp hx).1).2
  have hx'z := h.cent_z_of_cyc hc (mem_inf.mp (mem_inf.mp hx').1).2
  have hc' := h.mul_inv_mem_zpowers_z (h.conj_t_of_mem_XS hx) (h.conj_t_of_mem_XS hx')
    (h.conj_t_not_mem_of_cyc hc hx hxN) (h.conj_t_not_mem_of_cyc hc hx' hx'N)
  have hxc : x⁻¹ * ((x' * d.t * x'⁻¹ * d.t⁻¹) * (x * d.t * x⁻¹ * d.t⁻¹)⁻¹) * x =
      (x' * d.t * x'⁻¹ * d.t⁻¹) * (x * d.t * x⁻¹ * d.t⁻¹)⁻¹ := by
    rcases h.mem_zpowers_z_iff.mp hc' with h1 | h1 <;> rw [h1]
    · group
    · rw [mul_assoc, ← hxz]
      group
  refine mem_X_of ?_ ?_
  · calc x⁻¹ * x' * d.z = x⁻¹ * (x' * d.z) := by group
      _ = x⁻¹ * (d.z * x') := by rw [hx'z]
      _ = x⁻¹ * (d.z * x) * x⁻¹ * x' := by group
      _ = x⁻¹ * (x * d.z) * x⁻¹ * x' := by rw [hxz]
      _ = d.z * (x⁻¹ * x') := by group
  · rw [show x⁻¹ * x' * d.t * (x⁻¹ * x')⁻¹ =
        x⁻¹ * ((x' * d.t * x'⁻¹ * d.t⁻¹) * (x * d.t * x⁻¹ * d.t⁻¹)⁻¹) * x * d.t by group, hxc]
    exact mul_mem (mem_sup_left hc') (mem_sup_right (mem_zpowers _))

theorem card_XS_dvd [Finite G] (hc : d.Cyc) :
    Nat.card d.XS ∣ 2 * Nat.card (normalizer (d.ZR : Set G)) := by
  have hidx : ((d.XS ⊓ normalizer (d.ZR : Set G)).subgroupOf d.XS).index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    by_cases hex : ∃ x₀ ∈ d.XS, x₀ ∉ normalizer (d.ZR : Set G)
    · obtain ⟨x₀, hx₀, hx₀N⟩ := hex
      refine ⟨⟨x₀, hx₀⟩, fun b => ?_⟩
      by_cases hb : (b : G) ∈ normalizer (d.ZR : Set G)
      · exact Or.inr (mem_subgroupOf.mpr (mem_inf.mpr ⟨b.2, hb⟩))
      · left
        rw [mem_subgroupOf]
        refine mem_inf.mpr ⟨mul_mem b.2 hx₀, ?_⟩
        have hb' : (b : G)⁻¹ ∉ normalizer (d.ZR : Set G) := fun h' => hb (by
          simpa using inv_mem h')
        simpa using h.mul_mem_X_of_cyc hc (inv_mem b.2) hx₀ hb' hx₀N
    · push Not at hex
      exact ⟨1, fun b => Or.inr (mem_subgroupOf.mpr (mem_inf.mpr ⟨b.2, hex b b.2⟩))⟩
  have hcard := ((d.XS ⊓ normalizer (d.ZR : Set G)).subgroupOf d.XS).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  rw [← hcard, mul_comm 2]
  exact Nat.mul_dvd_mul (card_dvd_of_le inf_le_right) hidx

theorem card_range_omegaPerm_dvd [Finite G] (hc : d.Cyc) :
    Nat.card d.omegaPerm.range ∣ 2 ^ 11 * 3 ^ 5 * 5 * 17 := by
  have hX := h.card_XV_eq
  rw [Nat.card_coe_set_eq, h.ncard_Om hc] at hX
  have hS := h.card_XS_dvd hc
  rw [h.card_X] at hS
  have hXV : Nat.card d.XV ∣ 2 ^ 11 * (2 ^ 11 * 3 ^ 5 * 5 * 17) := by
    rw [hX, show 2 ^ 11 * (2 ^ 11 * 3 ^ 5 * 5 * 17) = 136 * (2 * ((2 ^ 17 * 3 ^ 5 * 5) * 2)) by
      norm_num]
    exact Nat.mul_dvd_mul_left 136 (hS.trans (Nat.mul_dvd_mul_left 2
      (Nat.mul_dvd_mul_right h.card_CHz 2)))
  have hker : 2 ^ 11 ∣ Nat.card d.omegaPerm.ker := by
    have hle : d.C₀.subgroupOf d.XV ≤ d.omegaPerm.ker := fun x hx => h.omegaPerm_eq_one x hx
    rw [← h.card_C₀, ← Nat.card_congr (subgroupOfEquivOfLe h.C₀_le_XV).toEquiv]
    exact card_dvd_of_le hle
  obtain ⟨k, hk⟩ := hker
  rw [card_eq_card_ker_mul_card_range d.omegaPerm, hk, mul_assoc] at hXV
  exact (Dvd.intro_left k rfl).trans (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hXV)

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
