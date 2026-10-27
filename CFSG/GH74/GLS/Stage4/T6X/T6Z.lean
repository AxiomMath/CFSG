module

public import CFSG.GH74.GLS.Stage4.T6X.T6Irr
public import CFSG.GH74.GLS.Stage4.T6Inv
public import CFSG.GH74.GLS.Stage4.T6X.T6Basic

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6X

open CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem z_not_mem_pGroup {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) {P : Subgroup G}
    (hP : IsPGroup p ↥P) : N.z ∉ P := by
  intro hz
  have := t6_odd_of_pGroup h.prime h.p_ne_two hP hz
  rw [h.sec5.loc.z_ord] at this
  exact absurd this (by decide)

theorem R₂_inf_K₁ {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) : R₂ N p ⊓ N.K₁ = ⊥ := by
  have hpg := R₂_pGroup N h.prime
  have hQ := h.ctx.C.Q₁ (R₂ N p ⊓ N.K₁) inf_le_right (fun k hk n hn => by
    refine ⟨R₂_norm N p (K₁_le_M₂ h hk) hn.1, ?_⟩
    exact N.K₁.mul_mem (N.K₁.mul_mem hk hn.2) (N.K₁.inv_mem hk))
  rcases hQ with hle | hle
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases t2C_zpowers_cases h.ctx.zz (hle hx) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx.1) (z_not_mem_pGroup h hpg)
  · exfalso
    exact z_not_mem_pGroup h hpg (hle h.sec5.loc.z_mem_K₁).1

theorem t6_X₂_irr {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) (Y : Subgroup G) (hY : Y ≤ N.X₂)
    (hH : ∀ x ∈ N.H, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) : Y = ⊥ ∨ Y = N.X₂ := by
  obtain ⟨F, iF, fF, φ, hcard, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₂
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact h.sec5.loc.q₂_odd
  have hY' : Y ≤ (uSub F).map φ := hX ▸ hY
  have := t6_irr_u hinj hodd hY' (fun t ht y hy => by
    have : φ t ∈ N.H ⊓ N.K₂ := by rw [hHK]; exact Subgroup.mem_map_of_mem φ ht
    exact hH _ this.1 y hy)
  rwa [← hX] at this

theorem R₂_cent {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) :
    ∀ r ∈ R₂ N p, ∀ x ∈ N.X₂, r * x * r⁻¹ = x := by
  have hpg := R₂_pGroup N h.prime
  have : Fact p.Prime := ⟨h.prime⟩
  have hX₂R : N.X₂ ≤ R₂ N p := X₂_le_R₂ h
  set C₀ : Subgroup G := N.X₂ ⊓ Subgroup.centralizer (R₂ N p : Set G) with hC₀
  have hC₀le : C₀ ≤ N.X₂ := inf_le_left
  have hC₀H : ∀ x ∈ N.H, ∀ y ∈ C₀, x * y * x⁻¹ ∈ C₀ := by
    intro x hx y hy
    refine ⟨h.sec5.loc.H_norm_X₂ x hx y hy.1, Subgroup.mem_centralizer_iff.2 (fun r hr => ?_)⟩
    have hxM : x ∈ M₂ N := H_le_M₂ h hx
    have hr' : x⁻¹ * r * x ∈ R₂ N p := by
      have := R₂_norm N p ((M₂ N).inv_mem hxM) hr
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hy.2 _ hr'
    calc r * (x * y * x⁻¹) = x * ((x⁻¹ * r * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * r * x)) * x⁻¹ := by rw [h1]
      _ = (x * y * x⁻¹) * r := by group
  have hne : C₀ ≠ ⊥ := by
    have hnil : Group.IsNilpotent ↥(R₂ N p) := hpg.isNilpotent
    have hnormal : (N.X₂.subgroupOf (R₂ N p)).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := (Subgroup.mem_normalizer_iff.1 (R₂_le_M₂ N p g.2) (n : G)).1 hn
      simpa using this⟩
    have hbot : N.X₂.subgroupOf (R₂ N p) ≠ ⊥ := by
      intro hb
      have hcard : Nat.card ↥N.X₂ = 1 := by
        have : N.X₂ = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          have : (⟨x, hX₂R hx⟩ : ↥(R₂ N p)) ∈ N.X₂.subgroupOf (R₂ N p) := hx
          rw [hb, Subgroup.mem_bot] at this
          simpa using congrArg Subtype.val this
        rw [this]; simp
      have hq : 3 ≤ N.q₂ := h.sec5.loc.q₂_ge
      have := h.sec5.loc.card_X₂
      omega
    have hc := hnil.inf_center_ne_bot_of_normal hbot
    obtain ⟨⟨a, ha⟩, hane⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hc)
    obtain ⟨haX, hacent⟩ := ha
    intro hbot0
    apply hane
    have haX' : (a : G) ∈ N.X₂ := haX
    have hacent' : (a : G) ∈ Subgroup.centralizer (R₂ N p : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have := Subgroup.mem_center_iff.1 hacent ⟨r, hr⟩
      simpa using congrArg Subtype.val this
    have hmem : (a : G) ∈ C₀ := ⟨haX', hacent'⟩
    rw [hbot0, Subgroup.mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  rcases t6_X₂_irr h C₀ hC₀le hC₀H with h1 | h1
  · exact absurd h1 hne
  · intro r hr x hx
    have hxC : x ∈ C₀ := h1 ▸ hx
    have := Subgroup.mem_centralizer_iff.1 hxC.2 r hr
    calc r * x * r⁻¹ = (x * r) * r⁻¹ := by rw [this]
      _ = x := by group

theorem R₂_odd {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) : Odd (Nat.card ↥(R₂ N p)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨k, hk⟩ := (R₂_pGroup N h.prime).exists_card_eq
  rw [hk]
  exact (h.prime.odd_of_ne_two h.p_ne_two).pow

theorem Cz_gen {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) {Y : Subgroup G} (hXY : N.X₂ ≤ Y)
    (hYodd : ∀ y ∈ Y, Odd (orderOf y)) (hYK : ∀ k ∈ N.K₁, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y)
    (hY1 : Y ⊓ N.K₁ = ⊥) (hYc : ∀ y ∈ Y, ∀ x ∈ N.X₂, y * x * y⁻¹ = x) :
    ∀ y ∈ Y, N.z * y * N.z⁻¹ = y → y ∈ N.X₂ := by
  intro y hyR hyz
  have hyzc : y * N.z = N.z * y := by
    calc y * N.z = (N.z * y * N.z⁻¹) * N.z := by rw [hyz]
      _ = N.z * y := by group
  obtain ⟨F, iF, fF, φ, hcard, hinj, hrange, hzφ, hX, hX', hw, hHK⟩ := h.coord.coord₂
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact h.sec5.loc.q₂_odd
  have h3 : 3 ≤ Nat.card F := by rw [hcard]; exact h.sec5.loc.q₂_ge
  have hyK₂ : ∀ g ∈ φ.range, y * g * y⁻¹ ∈ φ.range := by
    rw [hrange]; exact (h.Cnorm y hyzc).2
  have hyX : ∀ c : F, y * φ (sl2U c) * y⁻¹ = φ (sl2U c) := by
    intro c
    apply hYc y hyR
    rw [hX]; exact Subgroup.mem_map_of_mem φ (sl2U_mem_uSub c)
  obtain ⟨s, hs⟩ := t6_aut_X hinj hodd h3 hyK₂ hyX
  have hx₀X : φ (sl2U s) ∈ N.X₂ := by rw [hX]; exact Subgroup.mem_map_of_mem φ (sl2U_mem_uSub s)
  have hx₀R : φ (sl2U s) ∈ Y := hXY hx₀X
  have hy₁R : (φ (sl2U s))⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem hx₀R) hyR
  have hy₁K₂ : ∀ k ∈ N.K₂, ((φ (sl2U s))⁻¹ * y) * k = k * ((φ (sl2U s))⁻¹ * y) := by
    intro k hk
    rw [← hrange] at hk
    obtain ⟨g, rfl⟩ := hk
    have h1 := hs g
    calc (φ (sl2U s))⁻¹ * y * φ g
        = (φ (sl2U s))⁻¹ * (y * φ g * y⁻¹) * y := by group
      _ = (φ (sl2U s))⁻¹ * (φ (sl2U s) * φ g * (φ (sl2U s))⁻¹) * y := by rw [h1]
      _ = φ g * ((φ (sl2U s))⁻¹ * y) := by group
  have hy₁z : ((φ (sl2U s))⁻¹ * y) * N.z = N.z * ((φ (sl2U s))⁻¹ * y) :=
    hy₁K₂ N.z h.sec5.loc.z_mem_K₂
  obtain ⟨hn₁, -⟩ := h.Cnorm _ hy₁z
  have hy₁K₁ : ∀ k ∈ N.K₁, ((φ (sl2U s))⁻¹ * y) * k = k * ((φ (sl2U s))⁻¹ * y) := by
    intro k hk
    set y₁ : G := (φ (sl2U s))⁻¹ * y with hy₁
    have hc₁ : y₁ * k * y₁⁻¹ * k⁻¹ ∈ N.K₁ :=
      N.K₁.mul_mem (hn₁ k hk) (N.K₁.inv_mem hk)
    have hc₂ : y₁ * k * y₁⁻¹ * k⁻¹ ∈ Y := by
      have := hYK k hk y₁⁻¹ (Y.inv_mem hy₁R)
      have e : y₁ * k * y₁⁻¹ * k⁻¹ = y₁ * (k * y₁⁻¹ * k⁻¹) := by group
      rw [e]
      exact Y.mul_mem hy₁R this
    have hc : y₁ * k * y₁⁻¹ * k⁻¹ ∈ Y ⊓ N.K₁ := ⟨hc₂, hc₁⟩
    rw [hY1, Subgroup.mem_bot] at hc
    calc y₁ * k = (y₁ * k * y₁⁻¹ * k⁻¹) * k * y₁ := by group
      _ = k * y₁ := by rw [hc]; group
  have hy₁1 : (φ (sl2U s))⁻¹ * y = 1 := by
    refine h.Rodd _ hy₁z (hYodd _ hy₁R) ?_
    intro k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm h.sec5.loc.K_comm k).1 hk
    calc (φ (sl2U s))⁻¹ * y * (a * b) = ((φ (sl2U s))⁻¹ * y * a) * b := by group
      _ = (a * ((φ (sl2U s))⁻¹ * y)) * b := by rw [hy₁K₁ a ha]
      _ = a * (((φ (sl2U s))⁻¹ * y) * b) := by group
      _ = a * (b * ((φ (sl2U s))⁻¹ * y)) := by rw [hy₁K₂ b hb]
      _ = a * b * ((φ (sl2U s))⁻¹ * y) := by group
  have : y = φ (sl2U s) := by
    have := congrArg (fun w => φ (sl2U s) * w) hy₁1
    simpa using this
  rw [this]; exact hx₀X

theorem R₂_Cz {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) :
    ∀ y ∈ R₂ N p, N.z * y * N.z⁻¹ = y → y ∈ N.X₂ :=
  Cz_gen h (X₂_le_R₂ h) (fun _ hy => t6_odd_of_pGroup h.prime h.p_ne_two (R₂_pGroup N h.prime) hy)
    (fun _ hk _ hy => R₂_norm N p (K₁_le_M₂ h hk) hy) (R₂_inf_K₁ h) (R₂_cent h)

theorem R₂_inv_comm {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) :
    (∀ r ∈ R₂ N p, N.z * r * N.z⁻¹ * r ∈ N.X₂) ∧ ∀ r ∈ R₂ N p, ∀ s ∈ R₂ N p, ⁅r, s⁆ ∈ N.X₂ := by
  refine t6_inv_mod (R := R₂ N p) (X := N.X₂) ?_ (R₂_odd h) h.sec5.loc.z_ord
    (Subgroup.mem_normalizer_fintype (fun n hn => R₂_norm N p (z_mem_M₂ h) hn)) (R₂_Cz h)
  intro x hx r hr
  have := R₂_cent h r hr x hx
  calc x * r = (r * x * r⁻¹) * r := by rw [this]
    _ = r * x := by group

end CFSG.GH74.GLS.Stage4.Rest.T6X
