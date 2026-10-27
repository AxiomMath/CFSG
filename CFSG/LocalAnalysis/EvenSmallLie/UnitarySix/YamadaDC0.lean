module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDV1
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Data

variable (d : Data G)

abbrev E₈ : Subgroup G := d.V₁ ⊔ zpowers d.t

abbrev C₀' : Subgroup G := d.A₁ ⊔ d.E₈

end Data

theorem zmod_two_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : b = a := by
  revert a b; decide

theorem zmod_two_add_add_add (a b : ZMod 2) : a + b + a + b = 0 := by
  revert a b; decide

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem z_mem_H : d.z ∈ d.H := mem_centralizer_singleton_iff.mpr h.z_comm_t

theorem ZR_le_H : d.ZR ≤ d.H := sup_le (zpowers_le.mpr h.z_mem_H) zpowers_t_le_H

theorem mem_ZR_iff {x : G} : x ∈ d.ZR ↔ x ∈ zpowers d.z ∨ x * d.t ∈ zpowers d.z := by
  refine mem_sup_zpowers_iff h.t_sq fun b hb => ?_
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
  exact Commute.zpow_left (show Commute d.z d.t from h.z_comm_t) k

theorem z_mem_A₂ : d.z ∈ d.A₂ := h.A₄_le_A₂ h.z_mem_A₄

theorem conj_t_not_mem_zpowers_z [Finite G] (x : G) : x⁻¹ * d.t * x ∉ zpowers d.z := by
  intro hx
  rcases h.mem_zpowers_z_iff.mp hx with h1 | h1
  · apply h.t_ne_one
    have : d.t = x * (x⁻¹ * d.t * x) * x⁻¹ := by group
    rw [this, h1]; group
  · exact h.not_conj_mem_A₂ x (h1 ▸ h.z_mem_A₂)

theorem conj_t_of_mem_X [Finite G] {x : G} (hx : x ∈ normalizer (d.ZR : Set G)) :
    x⁻¹ * d.t * x = d.t ∨ x⁻¹ * d.t * x = d.z * d.t := by
  have h1 : x⁻¹ * d.t * x ∈ d.ZR :=
    (mem_normalizer_iff''.mp hx d.t).mp (mem_sup_right (mem_zpowers _))
  rcases h.mem_ZR_iff.mp h1 with h2 | h2
  · exact absurd h2 (h.conj_t_not_mem_zpowers_z x)
  · rcases h.mem_zpowers_z_iff.mp h2 with h3 | h3
    · left
      calc x⁻¹ * d.t * x = x⁻¹ * d.t * x * d.t * d.t := by rw [mul_assoc _ d.t d.t, h.t_sq,
            mul_one]
        _ = d.t := by rw [h3, one_mul]
    · right
      calc x⁻¹ * d.t * x = x⁻¹ * d.t * x * d.t * d.t := by rw [mul_assoc _ d.t d.t, h.t_sq,
            mul_one]
        _ = d.z * d.t := by rw [h3]

theorem X_le_cent_z [Finite G] {x : G} (hx : x ∈ normalizer (d.ZR : Set G)) :
    x ∈ centralizer ({d.z} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  have h1 : x⁻¹ * d.z * x ∈ d.ZR :=
    (mem_normalizer_iff''.mp hx d.z).mp (mem_sup_left (mem_zpowers _))
  obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
  have hz : x⁻¹ * d.z * x = d.z := by
    rcases h.mem_ZR_iff.mp h1 with h2 | h2
    · rcases h.mem_zpowers_z_iff.mp h2 with h3 | h3
      · exfalso; apply h.z_ne_one
        have : d.z = x * (x⁻¹ * d.z * x) * x⁻¹ := by group
        rw [this, h3]; group
      · exact h3
    · exfalso
      rcases h.mem_zpowers_z_iff.mp h2 with h3 | h3
      ·
        apply h.not_conj_mem_A₂ x⁻¹
        have : x⁻¹⁻¹ * d.t * x⁻¹ = d.z := by
          have e : x⁻¹ * d.z * x = d.t := by
            calc x⁻¹ * d.z * x = x⁻¹ * d.z * x * d.t * d.t := by
                  rw [mul_assoc _ d.t d.t, h.t_sq, mul_one]
              _ = d.t := by rw [h3, one_mul]
          rw [← e]; group
        rw [this]; exact h.z_mem_A₂
      ·
        apply h.not_conj_mem_A₂ (v * x⁻¹)
        have e : x⁻¹ * d.z * x = d.z * d.t := by
          calc x⁻¹ * d.z * x = x⁻¹ * d.z * x * d.t * d.t := by
                rw [mul_assoc _ d.t d.t, h.t_sq, mul_one]
            _ = d.z * d.t := by rw [h3]
        have : (v * x⁻¹)⁻¹ * d.t * (v * x⁻¹) = d.z := by
          calc (v * x⁻¹)⁻¹ * d.t * (v * x⁻¹) = x * (v⁻¹ * d.t * v) * x⁻¹ := by group
            _ = x * (x⁻¹ * d.z * x) * x⁻¹ := by rw [hvt, e]
            _ = d.z := by group
        rw [this]; exact h.z_mem_A₂
  calc x * d.z = x * (x⁻¹ * d.z * x) := by rw [hz]
    _ = d.z * x := by group

omit h in
theorem CHz_le_X [Finite G] : centralizer ({d.z} : Set G) ⊓ d.H ≤ normalizer (d.ZR : Set G) := by
  intro c hc
  obtain ⟨hcz, hcH⟩ := mem_inf.mp hc
  exact mem_normalizer_sup (mem_normalizer_zpowers (mem_centralizer_singleton_iff.mp hcz))
    (mem_normalizer_zpowers (mem_centralizer_singleton_iff.mp hcH))

theorem X_inf_H [Finite G] :
    normalizer (d.ZR : Set G) ⊓ d.H = centralizer ({d.z} : Set G) ⊓ d.H :=
  le_antisymm (fun _ hx => mem_inf.mpr ⟨h.X_le_cent_z (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩)
    (le_inf CHz_le_X inf_le_right)

theorem X_factor [Finite G] {x : G} (hx : x ∈ normalizer (d.ZR : Set G)) :
    ∃ v ∈ d.V₁, x * v⁻¹ ∈ centralizer ({d.z} : Set G) ⊓ d.H := by
  rcases h.conj_t_of_mem_X hx with h1 | h1
  · refine ⟨1, one_mem _, ?_⟩
    rw [inv_one, mul_one, ← h.X_inf_H]
    refine mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
    calc x * d.t = x * (x⁻¹ * d.t * x) := by rw [h1]
      _ = d.t * x := by group
  · obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
    refine ⟨v, hv, ?_⟩
    rw [← h.X_inf_H]
    refine mem_inf.mpr ⟨mul_mem hx (inv_mem (h.V₁_le_normalizer_ZR hv)),
      mem_centralizer_singleton_iff.mpr ?_⟩
    calc x * v⁻¹ * d.t = x * (v⁻¹ * d.t * v) * v⁻¹ := by group
      _ = x * (x⁻¹ * d.t * x) * v⁻¹ := by rw [hvt, h1]
      _ = d.t * (x * v⁻¹) := by group

theorem conj_t_V₁ [Finite G] {v : G} (hv : v ∈ d.V₁) :
    ∃ w ∈ zpowers d.z, v * d.t * v⁻¹ = w * d.t := by
  have hcr := h.crossed_V₁ (inv_mem hv)
  rw [inv_inv] at hcr
  exact ⟨_, hcr, by rw [mul_assoc _ d.t d.t, h.t_sq, mul_one]⟩

theorem commutator_mem_ZR [Finite G] {c v : G} (hc : c ∈ centralizer ({d.z} : Set G) ⊓ d.H)
    (hv : v ∈ d.V₁) : c⁻¹ * (v * c * v⁻¹) ∈ d.ZR := by
  obtain ⟨hcz, hcH⟩ := mem_inf.mp hc
  have hct : c * d.t = d.t * c := mem_centralizer_singleton_iff.mp hcH
  have hczz : c * d.z = d.z * c := mem_centralizer_singleton_iff.mp hcz
  obtain ⟨w, hw, hvt⟩ := h.conj_t_V₁ hv
  have hw' : w * w = 1 := by
    rcases h.mem_zpowers_z_iff.mp hw with rfl | rfl
    · simp
    · exact h.z_sq
  have hwc : c * w = w * c := by
    rcases h.mem_zpowers_z_iff.mp hw with rfl | rfl
    · simp
    · exact hczz
  have hwt : w * d.t = d.t * w := by
    rcases h.mem_zpowers_z_iff.mp hw with rfl | rfl
    · simp
    · exact h.z_comm_t
  have hvcH : v * c * v⁻¹ ∈ d.H := by
    change v * c * v⁻¹ ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have hvw : v⁻¹ * w * v = w := by
      have hwV : w ∈ d.V₁ := (zpowers_le.mpr h.z_mem_V₁) hw
      rw [mul_assoc, h.V₁_comm hwV hv]; group
    have e1 : v⁻¹ * d.t * v = w * d.t := by
      calc v⁻¹ * d.t * v = w * (w * (v⁻¹ * d.t * v)) := by rw [← mul_assoc, hw', one_mul]
        _ = w * ((v⁻¹ * w * v) * (v⁻¹ * d.t * v)) := by rw [hvw]
        _ = w * (v⁻¹ * (v * d.t * v⁻¹) * v) := by rw [hvt]; group
        _ = w * d.t := by group
    have hcwt : c * (w * d.t) = (w * d.t) * c := by
      rw [← mul_assoc, hwc, mul_assoc, hct, ← mul_assoc]
    calc v * c * v⁻¹ * d.t = v * c * (v⁻¹ * d.t * v) * v⁻¹ := by group
      _ = v * c * (w * d.t) * v⁻¹ := by rw [e1]
      _ = v * (w * d.t) * c * v⁻¹ := by rw [mul_assoc v c, hcwt]; group
      _ = v * (v⁻¹ * d.t * v) * c * v⁻¹ := by rw [e1]
      _ = d.t * (v * c * v⁻¹) := by group
  refine h.CH_A₁ (mem_inf.mpr ⟨?_, mul_mem (inv_mem hcH) hvcH⟩)
  rw [mem_centralizer_iff]
  intro a ha
  have hvA := h.V₁_le_cent_A₁ hv
  have hca : c * a * c⁻¹ ∈ d.A₁ := (mem_normalizer_iff.mp (h.CHz_le hc) a).mp ha
  have h1 : a * v = v * a := mem_centralizer_iff.mp hvA a ha
  have h2 : (c * a * c⁻¹) * v = v * (c * a * c⁻¹) := mem_centralizer_iff.mp hvA _ hca
  calc a * (c⁻¹ * (v * c * v⁻¹)) = c⁻¹ * ((c * a * c⁻¹) * v) * c * v⁻¹ := by group
    _ = c⁻¹ * (v * (c * a * c⁻¹)) * c * v⁻¹ := by rw [h2]
    _ = c⁻¹ * v * c * (a * v⁻¹) := by group
    _ = c⁻¹ * v * c * (v⁻¹ * a) := by
        rw [show a * v⁻¹ = v⁻¹ * a by
          calc a * v⁻¹ = v⁻¹ * (v * a) * v⁻¹ := by group
            _ = v⁻¹ * (a * v) * v⁻¹ := by rw [h1]
            _ = v⁻¹ * a := by group]
    _ = c⁻¹ * (v * c * v⁻¹) * a := by group

theorem z_cent_A₁ [Finite G] : d.z ∈ centralizer (d.A₁ : Set G) :=
  h.V₁_le_cent_A₁ h.z_mem_V₁

theorem t_cent_A₁ : d.t ∈ centralizer (d.A₁ : Set G) :=
  mem_centralizer_iff.mpr fun _ ha => h.comm_of_mem_L (h.A₁_le_L ha)

theorem t_mem_normalizer_V₁ [Finite G] : d.t ∈ normalizer (d.V₁ : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro v hv
  have e : d.t * v * d.t⁻¹ = v * (v⁻¹ * d.t * v * d.t) := by rw [h.t_inv]; group
  rw [e]
  exact mul_mem hv ((zpowers_le.mpr h.z_mem_V₁) (h.crossed_V₁ hv))

theorem t_not_mem_V₁ [Finite G] : d.t ∉ d.V₁ := by
  intro ht
  have := h.V₁_inf_H_le (mem_inf.mpr ⟨ht, t_mem_H⟩)
  rcases h.mem_zpowers_z_iff.mp this with h1 | h1
  · exact h.t_ne_one h1
  · exact h.t_not_mem_L (h1 ▸ h.A₄_le_L h.z_mem_A₄)

theorem mem_E₈_iff [Finite G] {x : G} : x ∈ d.E₈ ↔ x ∈ d.V₁ ∨ x * d.t⁻¹ ∈ d.V₁ :=
  mem_sup_zpowers_of_normalizer h.t_mem_normalizer_V₁ (by rw [h.t_sq]; exact one_mem _)

theorem E₈_le_cent_A₁ [Finite G] : d.E₈ ≤ centralizer (d.A₁ : Set G) :=
  sup_le h.V₁_le_cent_A₁ (zpowers_le.mpr h.t_cent_A₁)

theorem card_E₈ [Finite G] : Nat.card d.E₈ = 8 := by
  have hle : Nat.card d.E₈ ≤ 2 * 4 := by
    have := card_sup_zpowers_le h.t_mem_normalizer_V₁ (by rw [h.t_sq]; exact one_mem _)
    rwa [h.card_V₁] at this
  have hdvd : Nat.card d.V₁ ∣ Nat.card d.E₈ := Subgroup.card_dvd_of_le le_sup_left
  rw [h.card_V₁] at hdvd
  have hne : Nat.card d.E₈ ≠ 4 := by
    intro h4
    have heq : d.V₁ = d.E₈ := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h4, h.card_V₁])
    exact h.t_not_mem_V₁ (heq ▸ mem_sup_right (mem_zpowers _))
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card d.E₈ := Nat.card_pos
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk3 with rfl | rfl | rfl <;> omega

theorem isPGroup_E₈ [Finite G] : IsPGroup 2 d.E₈ :=
  IsPGroup.of_card (n := 3) (by rw [h.card_E₈]; norm_num)

theorem E₈_le_X [Finite G] : d.E₈ ≤ normalizer (d.ZR : Set G) :=
  sup_le (fun _ hv => h.V₁_le_normalizer_ZR hv)
    (zpowers_le.mpr (CHz_le_X (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr h.z_comm_t.symm,
      t_mem_H⟩)))

theorem A₁_le_CHz [Finite G] : d.A₁ ≤ centralizer ({d.z} : Set G) ⊓ d.H := fun a ha =>
  mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.z_cent_A₁ a ha),
    h.L_le_H (h.A₁_le_L ha)⟩

theorem C₀'_le_X [Finite G] : d.C₀' ≤ normalizer (d.ZR : Set G) :=
  sup_le (fun _ ha => CHz_le_X (h.A₁_le_CHz ha)) h.E₈_le_X

theorem isPGroup_C₀' [Finite G] : IsPGroup 2 d.C₀' := by
  refine IsPGroup.to_sup_of_normal_left' (IsPGroup.of_card h.card_A₁) h.isPGroup_E₈ ?_
  exact fun e he => centralizer_le_normalizer _ (h.E₈_le_cent_A₁ he)

theorem ZR_le_C₀' : d.ZR ≤ d.C₀' :=
  sup_le (zpowers_le.mpr (mem_sup_left h.z_mem_A₁)) (zpowers_le.mpr
    (mem_sup_right (mem_sup_right (mem_zpowers _))))

theorem X_le_normalizer_C₀' [Finite G] :
    normalizer (d.ZR : Set G) ≤ normalizer (d.C₀' : Set G) := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := h.X_factor hx
  have hvN : v ∈ normalizer (d.C₀' : Set G) :=
    Subgroup.le_normalizer (mem_sup_right (mem_sup_left hv))
  have hcN : x * v⁻¹ ∈ normalizer (d.C₀' : Set G) := by
    set c := x * v⁻¹ with hc
    obtain ⟨hcz, hcH⟩ := mem_inf.mp hxv
    apply mem_normalizer_of_conj_mem
    have hle : d.C₀' ≤ d.C₀'.comap (MulAut.conj c).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (sup_le (fun v' hv' => ?_) ?_)
      · exact mem_sup_left ((mem_normalizer_iff.mp (h.CHz_le hxv) a).mp ha)
      · change c * v' * c⁻¹ ∈ d.C₀'
        have hk := h.commutator_mem_ZR (c := c⁻¹) (inv_mem hxv) hv'
        rw [inv_inv] at hk
        have e : c * v' * c⁻¹ = (c * (v' * c⁻¹ * v'⁻¹)) * v' := by group
        rw [e]
        exact mul_mem (h.ZR_le_C₀' hk) (mem_sup_right (mem_sup_left hv'))
      · rw [zpowers_le]
        change c * d.t * c⁻¹ ∈ d.C₀'
        rw [mem_centralizer_singleton_iff.mp hcH, mul_inv_cancel_right]
        exact mem_sup_right (mem_sup_right (mem_zpowers _))
    exact fun y hy => hle hy
  have e : x = (x * v⁻¹) * v := by group
  rw [e]
  exact mul_mem hcN hvN

theorem C₀_eq [Finite G] : d.C₀ = d.C₀' := by
  have hle : d.C₀' ≤ d.C₀ := le_oTwo h.C₀'_le_X h.X_le_normalizer_C₀' h.isPGroup_C₀'
  refine le_antisymm (fun c hc => ?_) hle
  have hcX : c ∈ normalizer (d.ZR : Set G) := oTwo_le _ hc
  obtain ⟨v, hv, hcv⟩ := h.X_factor hcX
  have hvC : v ∈ d.C₀ := hle (mem_sup_right (mem_sup_left hv))
  have hP : d.C₀ ⊓ (centralizer ({d.z} : Set G) ⊓ d.H) ≤ d.withT d.A₁ := by
    refine h.oTwo_CHz _ inf_le_right ?_ ((isPGroup_oTwo _).to_le inf_le_left)
    intro y hy
    apply mem_normalizer_of_conj_mem
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_inf.mp hw
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (le_normalizer_oTwo _ (CHz_le_X hy)) w).mp hw1,
      (mem_normalizer_iff.mp (Subgroup.le_normalizer hy) w).mp hw2⟩
  have hcv' := hP (mem_inf.mpr ⟨mul_mem hc (inv_mem hvC), hcv⟩)
  have hT : d.withT d.A₁ ≤ d.C₀' :=
    sup_le le_sup_left (zpowers_le.mpr (mem_sup_right (mem_sup_right (mem_zpowers _))))
  have e : c = (c * v⁻¹) * v := by group
  rw [e]
  exact mul_mem (hT hcv') (mem_sup_right (mem_sup_left hv))

omit h in
theorem X_le_normalizer_C₀ : normalizer (d.ZR : Set G) ≤ normalizer (d.C₀ : Set G) :=
  le_normalizer_oTwo _

theorem C₀_inf_cent_A₁ [Finite G] : d.C₀ ⊓ centralizer (d.A₁ : Set G) = d.E₈ := by
  rw [h.C₀_eq]
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right h.E₈_le_cent_A₁)
  obtain ⟨hxC, hxA⟩ := mem_inf.mp hx
  obtain ⟨a, ha, e, he, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha e he => (mem_centralizer_iff.mp (h.E₈_le_cent_A₁ he) a ha)) hxC
  have haA : a ∈ centralizer (d.A₁ : Set G) := by
    have := mul_mem hxA (inv_mem (h.E₈_le_cent_A₁ he))
    simpa using this
  have haz := h.center_A₁ (mem_inf.mpr ⟨ha, haA⟩)
  exact mul_mem (mem_sup_left ((zpowers_le.mpr h.z_mem_V₁) haz)) he

theorem C₀_inf_H [Finite G] : d.C₀ ⊓ d.H = d.withT d.A₁ := by
  rw [h.C₀_eq]
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le le_sup_left
    (zpowers_le.mpr (mem_sup_right (mem_sup_right (mem_zpowers _)))))
    (h.withT_le_H h.A₁_le_L))
  obtain ⟨hxC, hxH⟩ := mem_inf.mp hx
  obtain ⟨a, ha, e, he, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha e he => (mem_centralizer_iff.mp (h.E₈_le_cent_A₁ he) a ha)) hxC
  have heH : e ∈ d.H := by
    have := mul_mem (inv_mem (h.L_le_H (h.A₁_le_L ha))) hxH
    simpa using this
  have hzA : zpowers d.z ≤ d.A₁ := zpowers_le.mpr h.z_mem_A₁
  rcases h.mem_E₈_iff.mp he with he1 | he1
  · exact mem_sup_left (mul_mem ha (hzA (h.V₁_inf_H_le (mem_inf.mpr ⟨he1, heH⟩))))
  · have h1 : e * d.t⁻¹ ∈ zpowers d.z :=
      h.V₁_inf_H_le (mem_inf.mpr ⟨he1, mul_mem heH (inv_mem t_mem_H)⟩)
    have e2 : a * e = (a * (e * d.t⁻¹)) * d.t := by group
    rw [e2]
    exact mul_mem (mem_sup_left (mul_mem ha (hzA h1))) (mem_sup_right (mem_zpowers _))

theorem conj_t_C₀ [Finite G] {c : G} (hc : c ∈ d.C₀) :
    c⁻¹ * d.t * c = d.t ∨ c⁻¹ * d.t * c = d.z * d.t :=
  h.conj_t_of_mem_X (oTwo_le _ hc)

theorem X_le_normalizer_A₁ [Finite G] : normalizer (d.ZR : Set G) ≤ normalizer (d.A₁ : Set G) := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := h.X_factor hx
  have e : x = (x * v⁻¹) * v := by group
  rw [e]
  exact mul_mem (h.CHz_le hxv) (centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun a ha => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) a ha)))

theorem X_le_normalizer_E₈ [Finite G] : normalizer (d.ZR : Set G) ≤ normalizer (d.E₈ : Set G) := by
  intro x hx
  rw [← h.C₀_inf_cent_A₁]
  exact mem_normalizer_of_conj_mem fun y hy =>
    mem_inf.mpr ⟨(mem_normalizer_iff.mp (X_le_normalizer_C₀ hx) y).mp (mem_inf.mp hy).1,
      conj_mem_centralizer (h.X_le_normalizer_A₁ hx) (mem_inf.mp hy).2⟩

theorem crossed_V₁_eq_z [Finite G] {v : G} (hv : v ∈ d.V₁) (hvz : v ∉ zpowers d.z) :
    v⁻¹ * d.t * v * d.t = d.z := by
  rcases h.mem_zpowers_z_iff.mp (h.crossed_V₁ hv) with h1 | h1
  · exfalso
    apply hvz
    refine h.V₁_inf_H_le (mem_inf.mpr ⟨hv, mem_centralizer_singleton_iff.mpr ?_⟩)
    exact ((crossed_eq_one_iff h.t_sq).mp h1)
  · exact h1

theorem mul_inv_mem_zpowers_z [Finite G] {v w : G} (hv : v ∈ d.V₁) (hw : w ∈ d.V₁)
    (hvz : v ∉ zpowers d.z) (hwz : w ∉ zpowers d.z) : w * v⁻¹ ∈ zpowers d.z := by
  have hU : ∀ {y}, y ∈ d.V₁ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.V₁_le_D hy)
  refine h.V₁_inf_H_le (mem_inf.mpr ⟨mul_mem hw (inv_mem hv), ?_⟩)
  change w * v⁻¹ ∈ centralizer ({d.t} : Set G)
  rw [mem_centralizer_singleton_iff, ← crossed_eq_one_iff h.t_sq,
    h.crossed_U₄_mul (hU hw) (inv_mem (hU hv)), h.crossed_U₄_inv (hU hv),
    h.crossed_V₁_eq_z hw hwz, h.crossed_V₁_eq_z hv hvz, mul_inv_cancel]

theorem X_le_normalizer_V₁ [Finite G] : normalizer (d.ZR : Set G) ≤ normalizer (d.V₁ : Set G) := by
  intro x hx
  apply mem_normalizer_of_conj_mem
  intro v hv
  have hxz : x * d.z = d.z * x := mem_centralizer_singleton_iff.mp (h.X_le_cent_z hx)
  by_cases hvz : v ∈ zpowers d.z
  · rcases h.mem_zpowers_z_iff.mp hvz with rfl | rfl
    · simp
    · rw [hxz, mul_inv_cancel_right]; exact h.z_mem_V₁
  have hE : x * v * x⁻¹ ∈ d.E₈ :=
    (mem_normalizer_iff.mp (h.X_le_normalizer_E₈ hx) v).mp (mem_sup_left hv)
  rcases h.mem_E₈_iff.mp hE with h1 | h1
  · exact h1
  · exfalso
    set v' := x * v * x⁻¹ * d.t⁻¹ with hv'
    have hxv : x * v * x⁻¹ = v' * d.t := by rw [hv']; group
    have hvZR : v ∉ d.ZR := fun hm => hvz (h.V₁_inf_H_le (mem_inf.mpr ⟨hv, h.ZR_le_H hm⟩))
    have hv'z : v' ∉ zpowers d.z := by
      intro hm
      apply hvZR
      have h2 : x * v * x⁻¹ ∈ d.ZR := by
        rw [hxv]
        exact mul_mem (mem_sup_left hm) (mem_sup_right (mem_zpowers _))
      have := (mem_normalizer_iff.mp hx v).mpr h2
      exact this
    have hv'V : v' ∈ d.V₁ := h1
    have hsq1 : (x * v * x⁻¹) * (x * v * x⁻¹) = v * v := by
      have hvv : v * v ∈ zpowers d.z :=
        h.V₁_inf_H_le (mem_inf.mpr ⟨mul_mem hv hv, mem_centralizer_singleton_iff.mpr (by
          rw [← crossed_eq_one_iff h.t_sq, h.crossed_U₄_mul (h.D_le_U₄ (h.V₁_le_D hv))
            (h.D_le_U₄ (h.V₁_le_D hv)), h.crossed_V₁_eq_z hv hvz, h.z_sq])⟩)
      have hc : x * (v * v) * x⁻¹ = v * v := by
        rcases h.mem_zpowers_z_iff.mp hvv with h3 | h3
        · rw [h3]; group
        · rw [h3, hxz]; group
      rw [← hc]; group
    have hsq2 : (v' * d.t) * (v' * d.t) = v' * v' * d.z := by
      have hc := h.crossed_V₁_eq_z hv'V hv'z
      calc (v' * d.t) * (v' * d.t) = v' * v' * (v'⁻¹ * d.t * v' * d.t) := by group
        _ = v' * v' * d.z := by rw [hc]
    obtain ⟨w, hw, hwv'⟩ : ∃ w ∈ zpowers d.z, v' = w * v :=
      ⟨v' * v⁻¹, h.mul_inv_mem_zpowers_z hv hv'V hvz hv'z, by group⟩
    have hwv : w * v = v * w := h.V₁_comm ((zpowers_le.mpr h.z_mem_V₁) hw) hv
    have hww : w * w = 1 := by
      rcases h.mem_zpowers_z_iff.mp hw with h3 | h3
      · rw [h3, one_mul]
      · rw [h3]; exact h.z_sq
    rw [hxv] at hsq1
    rw [hsq1] at hsq2
    have hvv : v' * v' = v * v := by
      calc v' * v' = w * (v * w) * v := by rw [hwv']; group
        _ = w * (w * v) * v := by rw [hwv]
        _ = (w * w) * (v * v) := by group
        _ = v * v := by rw [hww, one_mul]
    rw [hvv] at hsq2
    apply h.z_ne_one
    calc d.z = (v * v)⁻¹ * (v * v * d.z) := by group
      _ = (v * v)⁻¹ * (v * v) := by rw [← hsq2]
      _ = 1 := by group

theorem X_comm_zpowers_z [Finite G] {x w : G} (hx : x ∈ normalizer (d.ZR : Set G))
    (hw : w ∈ zpowers d.z) : x * w = w * x := by
  have hxz : x * d.z = d.z * x := mem_centralizer_singleton_iff.mp (h.X_le_cent_z hx)
  rcases h.mem_zpowers_z_iff.mp hw with rfl | rfl
  · simp
  · exact hxz

theorem K₁_le_cent_V₁ [Finite G] : d.K₁ ≤ centralizer (d.V₁ : Set G) := by
  classical
  have hKX : ∀ k ∈ d.K₁, k ∈ normalizer (d.ZR : Set G) := fun k hk =>
    CHz_le_X (mem_inf.mpr ⟨h.K₁_cent_z hk, h.L_le_H (h.K₁_le_L hk)⟩)
  obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
  have hvz : v ∉ zpowers d.z := by
    intro hm
    have hvH : v * d.t = d.t * v :=
      mem_centralizer_singleton_iff.mp (h.ZR_le_H (mem_sup_left hm))
    have h1 : v⁻¹ * d.t * v = d.t := by rw [mul_assoc, ← hvH]; group
    apply h.z_ne_one
    calc d.z = d.z * d.t * d.t⁻¹ := by group
      _ = d.t * d.t⁻¹ := by rw [← hvt, h1]
      _ = 1 := mul_inv_cancel _
  have hdich : ∀ k ∈ normalizer (d.ZR : Set G), k * v * k⁻¹ = v ∨ k * v * k⁻¹ = d.z * v := by
    intro k hk
    have hkv : k * v * k⁻¹ ∈ d.V₁ := (mem_normalizer_iff.mp (h.X_le_normalizer_V₁ hk) v).mp hv
    have hkvz : k * v * k⁻¹ ∉ zpowers d.z := by
      intro hm
      apply hvz
      have e : v = k * v * k⁻¹ := by
        calc v = k⁻¹ * (k * v * k⁻¹) * k := by group
          _ = (k * v * k⁻¹) * k⁻¹ * k := by rw [h.X_comm_zpowers_z (inv_mem hk) hm]
          _ = k * v * k⁻¹ := by group
      rw [e]
      exact hm
    rcases h.mem_zpowers_z_iff.mp (h.mul_inv_mem_zpowers_z hv hkv hvz hkvz) with h1 | h1
    · left; exact mul_inv_eq_one.mp h1
    · right; rw [← h1]; group
  have hzv : ∀ k ∈ normalizer (d.ZR : Set G), k * (d.z * v) * k⁻¹ = d.z * (k * v * k⁻¹) := by
    intro k hk
    rw [show k * (d.z * v) * k⁻¹ = (k * d.z) * v * k⁻¹ by group,
      h.X_comm_zpowers_z hk (mem_zpowers _)]
    group
  have hzv1 : d.z * v ≠ v := by
    intro he
    apply h.z_ne_one
    calc d.z = d.z * v * v⁻¹ := by group
      _ = 1 := by rw [he, mul_inv_cancel]
  let f : G → ZMod 2 := fun k => if k * v * k⁻¹ = v then 0 else 1
  have hfp : ∀ k, k * v * k⁻¹ = v → f k = 0 := fun k hk => by simp [f, hk]
  have hfn : ∀ k, k * v * k⁻¹ ≠ v → f k = 1 := fun k hk => by simp [f, hk]
  have hf : ∀ k ∈ normalizer (d.ZR : Set G), ∀ k' ∈ normalizer (d.ZR : Set G),
      f (k * k') = f k + f k' := by
    intro k hk k' hk'
    have e : (k * k') * v * (k * k')⁻¹ = k * (k' * v * k'⁻¹) * k⁻¹ := by group
    rcases hdich k hk with h1 | h1 <;> rcases hdich k' hk' with h2 | h2
    · rw [hfp k h1, hfp k' h2, hfp (k * k') (by rw [e, h2, h1])]; rfl
    · rw [hfp k h1, hfn k' (by rw [h2]; exact hzv1),
        hfn (k * k') (by rw [e, h2, hzv k hk, h1]; exact hzv1)]
      rfl
    · rw [hfn k (by rw [h1]; exact hzv1), hfp k' h2,
        hfn (k * k') (by rw [e, h2, h1]; exact hzv1)]
      rfl
    · rw [hfn k (by rw [h1]; exact hzv1), hfn k' (by rw [h2]; exact hzv1),
        hfp (k * k') (by rw [e, h2, hzv k hk, h1, ← mul_assoc, h.z_sq, one_mul])]
      decide
  have hf1 : f 1 = 0 := by simp [f]
  have hfinv : ∀ k ∈ normalizer (d.ZR : Set G), f k⁻¹ = f k := by
    intro k hk
    have := hf k hk k⁻¹ (inv_mem hk)
    rw [mul_inv_cancel, hf1] at this
    exact zmod_two_eq_of_add_eq_zero this.symm
  have hle : ⁅d.K₁, d.K₁⁆ ≤ centralizer ({v} : Set G) := by
    rw [commutator_le]
    intro k hk k' hk'
    have hX := hKX k hk
    have hX' := hKX k' hk'
    have h0 : f ⁅k, k'⁆ = 0 := by
      rw [commutatorElement_def, hf _ (mul_mem (mul_mem hX hX') (inv_mem hX)) _ (inv_mem hX'),
        hf _ (mul_mem hX hX') _ (inv_mem hX), hf _ hX _ hX', hfinv k hX, hfinv k' hX']
      exact zmod_two_add_add_add _ _
    rw [mem_centralizer_singleton_iff]
    have hc : ⁅k, k'⁆ * v * ⁅k, k'⁆⁻¹ = v := by
      by_contra hne
      rw [hfn _ hne] at h0
      exact one_ne_zero h0
    calc ⁅k, k'⁆ * v = ⁅k, k'⁆ * v * ⁅k, k'⁆⁻¹ * ⁅k, k'⁆ := by group
      _ = v * ⁅k, k'⁆ := by rw [hc]
  intro k hk
  have hkv : k * v = v * k := mem_centralizer_singleton_iff.mp (hle (h.K₁_perfect hk))
  rw [mem_centralizer_iff]
  intro u hu
  by_cases huz : u ∈ zpowers d.z
  · exact (h.X_comm_zpowers_z (hKX k hk) huz).symm
  · have hw := h.mul_inv_mem_zpowers_z hv hu hvz huz
    have e : u = (u * v⁻¹) * v := by group
    rw [e]
    calc u * v⁻¹ * v * k = (u * v⁻¹) * (v * k) := by group
      _ = (u * v⁻¹) * (k * v) := by rw [hkv]
      _ = k * (u * v⁻¹) * v := by rw [← mul_assoc, ← h.X_comm_zpowers_z (hKX k hk) hw]
      _ = k * (u * v⁻¹ * v) := by group

theorem NHA₁_eq [Finite G] :
    normalizer (d.A₁ : Set G) ⊓ d.H = centralizer ({d.z} : Set G) ⊓ d.H := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.CHz_le inf_le_right)
  obtain ⟨hxN, hxH⟩ := mem_inf.mp hx
  refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, hxH⟩
  have h1 : x * d.z * x⁻¹ ∈ d.A₁ := (mem_normalizer_iff.mp hxN d.z).mp h.z_mem_A₁
  have h2 : x * d.z * x⁻¹ ∈ centralizer (d.A₁ : Set G) := conj_mem_centralizer hxN h.z_cent_A₁
  rcases h.mem_zpowers_z_iff.mp (h.center_A₁ (mem_inf.mpr ⟨h1, h2⟩)) with h3 | h3
  · exfalso; apply h.z_ne_one
    calc d.z = x⁻¹ * (x * d.z * x⁻¹) * x := by group
      _ = 1 := by rw [h3]; group
  · calc x * d.z = x * d.z * x⁻¹ * x := by group
      _ = d.z * x := by rw [h3]

theorem normalizer_ZR_eq [Finite G] :
    normalizer (d.ZR : Set G) = (normalizer (d.A₁ : Set G) ⊓ d.H) ⊔ d.V₁ := by
  rw [h.NHA₁_eq]
  refine le_antisymm (fun x hx => ?_) (sup_le CHz_le_X fun _ hv => h.V₁_le_normalizer_ZR hv)
  obtain ⟨v, hv, hxv⟩ := h.X_factor hx
  have e : x = (x * v⁻¹) * v := by group
  rw [e]
  exact mul_mem (mem_sup_left hxv) (mem_sup_right hv)

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
