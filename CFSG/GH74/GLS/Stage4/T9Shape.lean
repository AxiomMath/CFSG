module

public import CFSG.GH74.GLS.Stage4.T9Syl
public import CFSG.GH74.GLS.Stage4.S6Core

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T9

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.T6 CFSG.GH74.BNPair
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem t9_mem_conjBy (g : G) (A : Subgroup G) (x : G) :
    x ∈ BNPair.conjBy g A ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have : g * ((MulAut.conj g⁻¹).toMonoidHom y) * g⁻¹ = y := by
      simp
      group
    rw [this]
    exact hy
  · intro hx
    refine Subgroup.mem_map.2 ⟨g * x * g⁻¹, hx, ?_⟩
    simp
    group

theorem t9_RA_card {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) :
    Nat.card ↥(RA N4.toT2N3 N4.p u) = N4.q₁ * N4.q₂ := by
  have h1 := R₂_card_RA h
  have h2 : Nat.card ↥(R₂ N4.toT2N3 N4.p) = N4.q₁ ^ 2 * N4.q₂ ^ 3 := hS6.R₂_card
  rw [h2] at h1
  have hq₂ : 0 < N4.q₂ := by have := h.sec5.loc.q₂_ge; omega
  have h3 : Nat.card ↥(RA N4.toT2N3 N4.p u) ^ 2 = (N4.q₁ * N4.q₂) ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left hq₂
    calc N4.q₂ * Nat.card ↥(RA N4.toT2N3 N4.p u) ^ 2 = N4.q₁ ^ 2 * N4.q₂ ^ 3 := h1.symm
      _ = N4.q₂ * (N4.q₁ * N4.q₂) ^ 2 := by ring
  exact Nat.pow_left_injective (by norm_num : (2:ℕ) ≠ 0) h3

theorem t9_H_normK {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {x : G} (hx : x ∈ N.H) :
    (∀ k ∈ N.K₁, x * k * x⁻¹ ∈ N.K₁) ∧ (∀ k ∈ N.K₂, x * k * x⁻¹ ∈ N.K₂) :=
  h.Cnorm x (h.sec5.loc.H_comm x hx _ h.sec5.loc.z_mem_H)

theorem t9_hinv_shape {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {A : Subgroup G}
    (hAK : A ≤ N.K₁ ⊔ N.K₂) (hAp : IsPGroup p ↥A) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAH : ∀ x ∈ N.H, ∀ y ∈ A, x * y * x⁻¹ ∈ A) (hcard : Nat.card ↥A = N.q₁ * N.q₂) :
    ∃ α β : Bool, A = (if α then N.X₁' else N.X₁) ⊔ (if β then N.X₂' else N.X₂) := by
  obtain ⟨A₁, A₂, hA₁K, hA₂K, hAeq, hcard', hc₁, hc₂, -, -⟩ := t6_hinv h hAK hAp hAab hAH
  have hloc := h.sec5.loc
  have hq₁ := hloc.q₁_ge
  have hq₂ := hloc.q₂_ge
  have hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x := fun x hx y hy => hloc.K_comm x (hA₁K hx) y (hA₂K hy)
  have hc₁' : Nat.card ↥A₁ = N.q₁ ∧ Nat.card ↥A₂ = N.q₂ := by
    rw [hcard'] at hcard
    rcases hc₁ with h1 | h1 <;> rcases hc₂ with h2 | h2
    · rw [h1, h2] at hcard; nlinarith
    · rw [h1, h2] at hcard; nlinarith
    · rw [h1, h2] at hcard; nlinarith
    · exact ⟨h1, h2⟩
  have hA₁eq : A₁ = A ⊓ N.K₁ := by
    apply le_antisymm
    · exact le_inf (hAeq ▸ le_sup_left) (hA₁K)
    · rintro x ⟨hxA, hxK⟩
      rw [hAeq] at hxA
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := (mem_sup_iff_of_comm hcomm _).1 hxA
      have ha₂K₁ : a₂ ∈ N.K₁ := by
        have : a₂ = a₁⁻¹ * (a₁ * a₂) := by group
        rw [this]
        exact N.K₁.mul_mem (N.K₁.inv_mem (hA₁K ha₁)) hxK
      have ha₂A : a₂ ∈ A := hAeq ▸ Subgroup.mem_sup_right ha₂
      rcases t2C_zpowers_cases h.ctx.zz (hloc.K_inter ⟨ha₂K₁, hA₂K ha₂⟩) with h1 | h1
      · rw [h1, mul_one]; exact ha₁
      · exact absurd (h1 ▸ ha₂A) (z_not_mem_pGroup h hAp)
  have hA₂eq : A₂ = A ⊓ N.K₂ := by
    apply le_antisymm
    · exact le_inf (hAeq ▸ le_sup_right) (hA₂K)
    · rintro x ⟨hxA, hxK⟩
      rw [hAeq] at hxA
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := (mem_sup_iff_of_comm hcomm _).1 hxA
      have ha₁K₂ : a₁ ∈ N.K₂ := by
        have : a₁ = (a₁ * a₂) * a₂⁻¹ := by group
        rw [this]
        exact N.K₂.mul_mem hxK (N.K₂.inv_mem (hA₂K ha₂))
      have ha₁A : a₁ ∈ A := hAeq ▸ Subgroup.mem_sup_left ha₁
      rcases t2C_zpowers_cases h.ctx.zz (hloc.K_inter ⟨hA₁K ha₁, ha₁K₂⟩) with h1 | h1
      · rw [h1, one_mul]; exact ha₂
      · exact absurd (h1 ▸ ha₁A) (z_not_mem_pGroup h hAp)
  have hA₁H : ∀ x ∈ N.H, ∀ y ∈ A₁, x * y * x⁻¹ ∈ A₁ := by
    intro x hx y hy
    rw [hA₁eq] at hy ⊢
    exact ⟨hAH x hx y hy.1, (t9_H_normK h hx).1 y hy.2⟩
  have hA₂H : ∀ x ∈ N.H, ∀ y ∈ A₂, x * y * x⁻¹ ∈ A₂ := by
    intro x hx y hy
    rw [hA₂eq] at hy ⊢
    exact ⟨hAH x hx y hy.1, (t9_H_normK h hx).2 y hy.2⟩
  have hpA₁ : IsPGroup p ↥A₁ := hAp.to_le (hAeq ▸ le_sup_left)
  have hpA₂ : IsPGroup p ↥A₂ := hAp.to_le (hAeq ▸ le_sup_right)
  have h1 := t9_syl₁ h hA₁K hpA₁ hA₁H hc₁'.1
  have h2 := t9_syl₂ h hA₂K hpA₂ hA₂H hc₁'.2
  rw [hAeq]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact ⟨false, false, by simp [h1, h2]⟩
  · exact ⟨false, true, by simp [h1, h2]⟩
  · exact ⟨true, false, by simp [h1, h2]⟩
  · exact ⟨true, true, by simp [h1, h2]⟩

theorem t9_conj_shape {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {R : Subgroup G} {g : G}
    (hg : ∀ x ∈ N.H, g⁻¹ * x * g ∈ N.H) (hcard : Nat.card ↥R = N.q₁ * N.q₂)
    (hRp : IsPGroup p ↥R) (hRab : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r)
    (hRH : ∀ x ∈ N.H, ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hRK : ∀ r ∈ R, g * r * g⁻¹ ∈ N.K₁ ⊔ N.K₂) :
    ∃ α β : Bool, R = BNPair.conjBy g ((if α then N.X₁' else N.X₁) ⊔ (if β then N.X₂' else N.X₂)) := by
  set A' : Subgroup G := R.map (MulAut.conj g).toMonoidHom with hA'
  have hmem : ∀ y, y ∈ A' ↔ ∃ r ∈ R, g * r * g⁻¹ = y := by
    intro y
    simp [hA', Subgroup.mem_map]
  have hAK : A' ≤ N.K₁ ⊔ N.K₂ := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := (hmem y).1 hy
    exact hRK r hr
  have hAp : IsPGroup p ↥A' := hRp.map _
  have hAab : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    obtain ⟨r, hr, rfl⟩ := (hmem x).1 hx
    obtain ⟨s, hs, rfl⟩ := (hmem y).1 hy
    have := hRab r hr s hs
    calc g * r * g⁻¹ * (g * s * g⁻¹) = g * (r * s) * g⁻¹ := by group
      _ = g * (s * r) * g⁻¹ := by rw [this]
      _ = g * s * g⁻¹ * (g * r * g⁻¹) := by group
  have hAH : ∀ x ∈ N.H, ∀ y ∈ A', x * y * x⁻¹ ∈ A' := by
    intro x hx y hy
    obtain ⟨r, hr, rfl⟩ := (hmem y).1 hy
    refine (hmem _).2 ⟨(g⁻¹ * x * g) * r * (g⁻¹ * x * g)⁻¹, hRH _ (hg x hx) r hr, ?_⟩
    group
  have hcardA : Nat.card ↥A' = N.q₁ * N.q₂ := by
    rw [← hcard]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨α, β, hAeq⟩ := t9_hinv_shape h hAK hAp hAab hAH hcardA
  refine ⟨α, β, ?_⟩
  rw [← hAeq]
  ext x
  rw [t9_mem_conjBy]
  constructor
  · intro hx
    exact (hmem _).2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨r, hr, hrx⟩ := (hmem _).1 hx
    have : r = x := by
      have := congrArg (fun y => g⁻¹ * y * g) hrx
      simpa using this
    rwa [← this]

theorem t9_RA_shape {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) :
    ∃ α β : Bool, RA N4.toT2N3 N4.p u = BNPair.conjBy N4.a
      ((if α then N4.X₁' else N4.X₁) ⊔ (if β then N4.X₂' else N4.X₂)) :=
  t9_conj_shape h (fun _ hx => (a_normH h hx).1) (t9_RA_card h hS6) (RA_pGroup h) (RA_inv h).2
    (fun _ hx _ hr => RA_H h hx hr) (fun _ hr => RA_conj_K h hr)

theorem t9_RC_H {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {v : G}
    (hv : ∀ x ∈ N.H, x * v = v * x) {x : G} (hx : x ∈ N.H) {r : G}
    (hr : r ∈ R₂ N p ⊓ Subgroup.centralizer {v}) : x * r * x⁻¹ ∈ R₂ N p ⊓ Subgroup.centralizer {v} := by
  refine ⟨R₂_norm N p (H_le_M₂ h hx) hr.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hrv : r * v = v * r := Subgroup.mem_centralizer_singleton_iff.1 hr.2
  have hxv : x * v = v * x := hv x hx
  show x * r * x⁻¹ * v = v * (x * r * x⁻¹)
  calc x * r * x⁻¹ * v = x * r * (x⁻¹ * v) := by group
    _ = x * r * (v * x⁻¹) := by
      have : x⁻¹ * v = v * x⁻¹ := by
        calc x⁻¹ * v = x⁻¹ * (v * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * v) * x⁻¹ := by rw [hxv]
          _ = v * x⁻¹ := by group
      rw [this]
    _ = x * (r * v) * x⁻¹ := by group
    _ = x * (v * r) * x⁻¹ := by rw [hrv]
    _ = (x * v) * r * x⁻¹ := by group
    _ = (v * x) * r * x⁻¹ := by rw [hxv]
    _ = v * (x * r * x⁻¹) := by group

theorem t9_RB_inv {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) :
    (∀ b ∈ RB N p u, N.z * b * N.z⁻¹ = b⁻¹) ∧ ∀ b ∈ RB N p u, ∀ b' ∈ RB N p u, b * b' = b' * b := by
  have hw₁K : N.w₁ ∈ N.K₁ := h.sec5.loc.w₁_mem
  have hw₁z : N.w₁ * N.z = N.z * N.w₁ := h.ctx.C.zc₁ N.w₁ hw₁K
  have hrec : ∀ b ∈ RB N p u, b = N.w₁ * (N.w₁⁻¹ * b * N.w₁) * N.w₁⁻¹ := fun b _ => by group
  have hw : N.z * N.w₁ = N.w₁ * N.z := hw₁z.symm
  have hw' : N.w₁⁻¹ * N.z⁻¹ = N.z⁻¹ * N.w₁⁻¹ := by
    have := congrArg (fun x => x⁻¹) hw
    simpa [mul_inv_rev] using this
  refine ⟨fun b hb => ?_, fun b hb b' hb' => ?_⟩
  · obtain ⟨r, hrA, hbr⟩ : ∃ r ∈ RA N p u, b = N.w₁ * r * N.w₁⁻¹ :=
      ⟨N.w₁⁻¹ * b * N.w₁, RB_conj h hb, by group⟩
    have h1 := (RA_inv h).1 r hrA
    rw [hbr]
    calc N.z * (N.w₁ * r * N.w₁⁻¹) * N.z⁻¹ = (N.z * N.w₁) * r * (N.w₁⁻¹ * N.z⁻¹) := by group
      _ = (N.w₁ * N.z) * r * (N.z⁻¹ * N.w₁⁻¹) := by rw [hw, hw']
      _ = N.w₁ * (N.z * r * N.z⁻¹) * N.w₁⁻¹ := by group
      _ = N.w₁ * r⁻¹ * N.w₁⁻¹ := by rw [h1]
      _ = (N.w₁ * r * N.w₁⁻¹)⁻¹ := by group
  · have h1 := (RA_inv h).2 _ (RB_conj h hb) _ (RB_conj h hb')
    have : N.w₁ * (N.w₁⁻¹ * b * N.w₁ * (N.w₁⁻¹ * b' * N.w₁)) * N.w₁⁻¹ =
        N.w₁ * (N.w₁⁻¹ * b' * N.w₁ * (N.w₁⁻¹ * b * N.w₁)) * N.w₁⁻¹ := by rw [h1]
    calc b * b' = N.w₁ * (N.w₁⁻¹ * b * N.w₁ * (N.w₁⁻¹ * b' * N.w₁)) * N.w₁⁻¹ := by group
      _ = N.w₁ * (N.w₁⁻¹ * b' * N.w₁ * (N.w₁⁻¹ * b * N.w₁)) * N.w₁⁻¹ := this
      _ = b' * b := by group

theorem t9_a_facts {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) :
    N.a * (N.z * u) * N.a⁻¹ = u ∧ N.a ^ 2 * N.z * (N.a ^ 2)⁻¹ = u ∧
      N.a ^ 2 * (N.z * u) * (N.a ^ 2)⁻¹ = N.z := by
  obtain ⟨ha1, ha2⟩ := a_conj_facts h
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have e0 : N.a * (N.z * u) * N.a⁻¹ = u := by
    calc N.a * (N.z * u) * N.a⁻¹ = (N.a * N.z * N.a⁻¹) * (N.a * u * N.a⁻¹) := by group
      _ = (N.z * u) * N.z := by rw [ha1, ha2]
      _ = (u * N.z) * N.z := by rw [hzu]
      _ = u * (N.z * N.z) := by group
      _ = u := by rw [hz2, mul_one]
  refine ⟨e0, ?_, ?_⟩
  · calc N.a ^ 2 * N.z * (N.a ^ 2)⁻¹ = N.a * (N.a * N.z * N.a⁻¹) * N.a⁻¹ := by rw [pow_two]; group
      _ = u := by rw [ha2, e0]
  · calc N.a ^ 2 * (N.z * u) * (N.a ^ 2)⁻¹ = N.a * (N.a * (N.z * u) * N.a⁻¹) * N.a⁻¹ := by
          rw [pow_two]; group
      _ = N.z := by rw [e0, ha1]

theorem t9_RB_conj_K {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {r : G}
    (hr : r ∈ RB N p u) : N.a ^ 2 * r * (N.a ^ 2)⁻¹ ∈ N.K₁ ⊔ N.K₂ := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  obtain ⟨-, e2, e1⟩ := t9_a_facts h
  have hpg := R₂_pGroup N h.prime
  have hrc : r * (N.z * u) = (N.z * u) * r := Subgroup.mem_centralizer_singleton_iff.1 hr.2
  have hodd : Odd (orderOf (N.a ^ 2 * r * (N.a ^ 2)⁻¹)) := by
    have hdvd : orderOf (N.a ^ 2 * r * (N.a ^ 2)⁻¹) ∣ orderOf r := by
      apply orderOf_dvd_of_pow_eq_one
      rw [conj_pow, pow_orderOf_eq_one]
      group
    exact Odd.of_dvd_nat (t6_odd_of_pGroup h.prime h.p_ne_two hpg hr.1) hdvd
  refine t6_pelt_K h ?_ hodd (v := u) h.sec5.loc.u_mem_S ?_
  · calc N.a ^ 2 * r * (N.a ^ 2)⁻¹ * N.z
        = N.a ^ 2 * r * (N.a ^ 2)⁻¹ * (N.a ^ 2 * (N.z * u) * (N.a ^ 2)⁻¹) := by rw [e1]
      _ = N.a ^ 2 * (r * (N.z * u)) * (N.a ^ 2)⁻¹ := by group
      _ = N.a ^ 2 * ((N.z * u) * r) * (N.a ^ 2)⁻¹ := by rw [hrc]
      _ = (N.a ^ 2 * (N.z * u) * (N.a ^ 2)⁻¹) * (N.a ^ 2 * r * (N.a ^ 2)⁻¹) := by group
      _ = N.z * (N.a ^ 2 * r * (N.a ^ 2)⁻¹) := by rw [e1]
  · rw [← e2]
    calc N.a ^ 2 * N.z * (N.a ^ 2)⁻¹ * (N.a ^ 2 * r * (N.a ^ 2)⁻¹) * (N.a ^ 2 * N.z * (N.a ^ 2)⁻¹)⁻¹
        = N.a ^ 2 * (N.z * r * N.z⁻¹) * (N.a ^ 2)⁻¹ := by group
      _ = N.a ^ 2 * r⁻¹ * (N.a ^ 2)⁻¹ := by rw [(t9_RB_inv h).1 r hr]
      _ = (N.a ^ 2 * r * (N.a ^ 2)⁻¹)⁻¹ := by group

theorem t9_RB_shape {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) :
    ∃ γ δ : Bool, RB N4.toT2N3 N4.p u = BNPair.conjBy (N4.a ^ 2)
      ((if γ then N4.X₁' else N4.X₁) ⊔ (if δ then N4.X₂' else N4.X₂)) := by
  have hg : ∀ x ∈ N4.H, (N4.a ^ 2)⁻¹ * x * N4.a ^ 2 ∈ N4.H := by
    intro x hx
    have h1 := (a_normH h hx).1
    have h2 := (a_normH h h1).1
    have : (N4.a ^ 2)⁻¹ * x * N4.a ^ 2 = N4.a⁻¹ * (N4.a⁻¹ * x * N4.a) * N4.a := by
      rw [pow_two]; group
    rw [this]
    exact h2
  have hcard : Nat.card ↥(RB N4.toT2N3 N4.p u) = N4.q₁ * N4.q₂ := by
    rw [RA_card_eq_RB h]
    exact t9_RA_card h hS6
  have hHv : ∀ x ∈ N4.H, x * (N4.toT2N3.z * u) = (N4.toT2N3.z * u) * x := by
    intro x hx
    have hz := h.sec5.loc.H_comm x hx _ h.sec5.loc.z_mem_H
    have hu := h.sec5.loc.H_comm x hx _ h.sec5.loc.u_mem_H
    calc x * (N4.toT2N3.z * u) = (x * N4.toT2N3.z) * u := by group
      _ = (N4.toT2N3.z * x) * u := by rw [hz]
      _ = N4.toT2N3.z * (x * u) := by group
      _ = N4.toT2N3.z * (u * x) := by rw [hu]
      _ = (N4.toT2N3.z * u) * x := by group
  exact t9_conj_shape h hg hcard ((R₂_pGroup _ h.prime).to_le inf_le_left) (t9_RB_inv h).2
    (fun x hx r hr => t9_RC_H h hHv hx hr) (fun r hr => t9_RB_conj_K h hr)

theorem t9_P_split {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6)
    {x : G} (hx : x ∈ N4.P) : ∃ r ∈ R₂ N4.toT2N3 N4.p, ∃ y ∈ N4.X₁, x = r * y := by
  have hX₁K : N4.X₁ ≤ N4.K₁ := X₁_le_K₁ h
  have hnorm : N4.X₁ ≤ normalizer (R₂ N4.toT2N3 N4.p : Set G) := by
    intro y hy
    apply Subgroup.mem_normalizer_fintype
    intro r hr
    exact hS6.K₁_normR₂ y (hX₁K hy) r hr
  have hP : N4.P = R₂ N4.toT2N3 N4.p ⊔ N4.X₁ := hS6.P_eq
  rw [hP] at hx
  obtain ⟨r, hr, y, hy, rfl⟩ := t2P53_split hnorm hx
  exact ⟨r, hr, y, hy, rfl⟩

omit [Finite G] in
theorem t9_R₂_le_P {N4 : T2N4 G} (hS6 : S6Shape N4.toCh6) : R₂ N4.toT2N3 N4.p ≤ N4.P := by
  have hP : N4.P = R₂ N4.toT2N3 N4.p ⊔ N4.X₁ := hS6.P_eq
  rw [hP]; exact le_sup_left

omit [Finite G] in
theorem t9_X₁_le_P {N4 : T2N4 G} (hS6 : S6Shape N4.toCh6) : N4.X₁ ≤ N4.P := by
  have hP : N4.P = R₂ N4.toT2N3 N4.p ⊔ N4.X₁ := hS6.P_eq
  rw [hP]; exact le_sup_right

theorem t9_X₁_odd {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6)
    {y : G} (hy : y ∈ N4.X₁) : Odd (orderOf y) :=
  t6_odd_of_pGroup h.prime h.p_ne_two hS6.P_pGroup (t9_X₁_le_P hS6 hy)

theorem t9_cent_P {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) {v : G}
    (hvM : v ∈ M₂ N4.toT2N3) (hv : ∀ y ∈ N4.X₁, v * y * v⁻¹ = y⁻¹) :
    Subgroup.centralizer {v} ⊓ N4.P = R₂ N4.toT2N3 N4.p ⊓ Subgroup.centralizer {v} := by
  apply le_antisymm
  · rintro x ⟨hxv, hxP⟩
    have hxv' : x * v = v * x := (Subgroup.mem_centralizer_singleton_iff.1 hxv).symm.symm
    obtain ⟨r, hr, y, hy, rfl⟩ := t9_P_split h hS6 hxP
    have hr' : v * r * v⁻¹ ∈ R₂ N4.toT2N3 N4.p := R₂_norm N4.toT2N3 N4.p hvM hr
    have e1 : v * (r * y) * v⁻¹ = r * y := by
      calc v * (r * y) * v⁻¹ = (r * y) * v * v⁻¹ := by rw [← hxv']
        _ = r * y := by group
    have e2 : v * (r * y) * v⁻¹ = (v * r * v⁻¹) * y⁻¹ := by
      calc v * (r * y) * v⁻¹ = (v * r * v⁻¹) * (v * y * v⁻¹) := by group
        _ = (v * r * v⁻¹) * y⁻¹ := by rw [hv y hy]
    have e3 : y * y ∈ R₂ N4.toT2N3 N4.p := by
      have : y * y = r⁻¹ * (v * r * v⁻¹) := by
        have h1 : (v * r * v⁻¹) * y⁻¹ = r * y := by rw [← e2, e1]
        have h2 : r⁻¹ * ((v * r * v⁻¹) * y⁻¹) = y := by rw [h1]; group
        calc y * y = (r⁻¹ * ((v * r * v⁻¹) * y⁻¹)) * y := by rw [h2]
          _ = r⁻¹ * (v * r * v⁻¹) := by group
      rw [this]
      exact (R₂ N4.toT2N3 N4.p).mul_mem ((R₂ N4.toT2N3 N4.p).inv_mem hr) hr'
    have hK₁ : y * y ∈ N4.K₁ := N4.K₁.mul_mem (X₁_le_K₁ h hy) (X₁_le_K₁ h hy)
    have hbot : y * y ∈ R₂ N4.toT2N3 N4.p ⊓ N4.K₁ := ⟨e3, hK₁⟩
    rw [R₂_inf_K₁ h, Subgroup.mem_bot] at hbot
    have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact hbot
    have hy1 : y = 1 := by
      have hodd := t9_X₁_odd h hS6 hy
      have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h4 | h4
      · exact orderOf_eq_one_iff.1 h4
      · rw [h4] at hodd; exact absurd hodd (by decide)
    subst hy1
    rw [mul_one] at hxv' ⊢
    exact ⟨hr, Subgroup.mem_centralizer_singleton_iff.2 hxv'.symm.symm⟩
  · rintro x ⟨hxR, hxv⟩
    exact ⟨hxv, t9_R₂_le_P hS6 hxR⟩

theorem t9_X₂_zu_fix {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {x : G} (hx : x ∈ N.X₂)
    (hxu : x * (N.z * u) = (N.z * u) * x) : x = 1 := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have hpg := R₂_pGroup N h.prime
  have hxK : x ∈ N.K₂ := by rw [h.sec5.loc.K₂_eq]; exact Subgroup.mem_sup_left hx
  have hxz : N.z * x = x * N.z := (h.ctx.C.zc₂ x hxK).symm
  have h1 : (N.z * u) * x * (N.z * u)⁻¹ = x⁻¹ := by
    have e : (N.z * u) * x * (N.z * u)⁻¹ = N.z * (u * x * u⁻¹) * N.z⁻¹ := by group
    rw [e, h.sec5.loc.u_inv_X₂ x hx]
    calc N.z * x⁻¹ * N.z⁻¹ = (N.z * x * N.z⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [hxz]; group
  have h2 : (N.z * u) * x * (N.z * u)⁻¹ = x := by
    calc (N.z * u) * x * (N.z * u)⁻¹ = (x * (N.z * u)) * (N.z * u)⁻¹ := by rw [hxu]
      _ = x := by group
  have h3 : x * x = 1 := by
    have : x = x⁻¹ := by rw [← h1, h2]
    calc x * x = x * x⁻¹ := by rw [← this]
      _ = 1 := by group
  have hodd := t6_odd_of_pGroup h.prime h.p_ne_two hpg (X₂_le_R₂ h hx)
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h4 | h4
  · exact orderOf_eq_one_iff.1 h4
  · rw [h4] at hodd; exact absurd hodd (by decide)

theorem t9_u_RB {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {t : G} (ht : t ∈ RB N p u) :
    u * t * u⁻¹ = t⁻¹ := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have htc : t * (N.z * u) = (N.z * u) * t := Subgroup.mem_centralizer_singleton_iff.1 ht.2
  have hzt := (t9_RB_inv h).1 t ht
  have hzinv : N.z⁻¹ = N.z := inv_eq_of_mul_eq_one_right hz2
  calc u * t * u⁻¹ = (N.z * N.z) * (u * t * u⁻¹) * (N.z * N.z)⁻¹ := by rw [hz2]; group
    _ = N.z * ((N.z * u) * t * (N.z * u)⁻¹) * N.z⁻¹ := by group
    _ = N.z * t * N.z⁻¹ := by
      congr 2
      calc (N.z * u) * t * (N.z * u)⁻¹ = (t * (N.z * u)) * (N.z * u)⁻¹ := by rw [htc]
        _ = t := by group
    _ = t⁻¹ := hzt

theorem t9_prod_inj {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {x x' s s' t t' : G}
    (hx : x ∈ N.X₂) (hx' : x' ∈ N.X₂) (hs : s ∈ RA N p u) (hs' : s' ∈ RA N p u)
    (ht : t ∈ RB N p u) (ht' : t' ∈ RB N p u) (heq : x * s * t = x' * s' * t') :
    x = x' ∧ s = s' ∧ t = t' := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have hpg := R₂_pGroup N h.prime
  have hcent : ∀ r ∈ R₂ N p, ∀ y ∈ N.X₂, r * y = y * r := fun r hr y hy => by
    have := R₂_cent h r hr y hy
    calc r * y = (r * y * r⁻¹) * r := by group
      _ = y * r := by rw [this]
  have hsR : s ∈ R₂ N p := hs.1
  have hs'R : s' ∈ R₂ N p := hs'.1
  have htR : t ∈ R₂ N p := ht.1
  have ht'R : t' ∈ R₂ N p := ht'.1
  have hyX : x⁻¹ * x' ∈ N.X₂ := N.X₂.mul_mem (N.X₂.inv_mem hx) hx'
  set y := x⁻¹ * x' with hy
  have hyinv : y⁻¹ ∈ N.X₂ := N.X₂.inv_mem hyX
  have E0 : s * t = y * (s' * t') := by
    calc s * t = x⁻¹ * (x * s * t) := by group
      _ = x⁻¹ * (x' * s' * t') := by rw [heq]
      _ = y * (s' * t') := by rw [hy]; group
  have hus : u * s * u⁻¹ = s := by
    have : s * u = u * s := Subgroup.mem_centralizer_singleton_iff.1 hs.2
    calc u * s * u⁻¹ = (s * u) * u⁻¹ := by rw [this]
      _ = s := by group
  have hus' : u * s' * u⁻¹ = s' := by
    have : s' * u = u * s' := Subgroup.mem_centralizer_singleton_iff.1 hs'.2
    calc u * s' * u⁻¹ = (s' * u) * u⁻¹ := by rw [this]
      _ = s' := by group
  have hut := t9_u_RB h ht
  have hut' := t9_u_RB h ht'
  have huy : u * y * u⁻¹ = y⁻¹ := h.sec5.loc.u_inv_X₂ y hyX
  have Eu : s * t⁻¹ = y⁻¹ * (s' * t'⁻¹) := by
    have := congrArg (fun g => u * g * u⁻¹) E0
    calc s * t⁻¹ = (u * s * u⁻¹) * (u * t * u⁻¹) := by rw [hus, hut]
      _ = u * (s * t) * u⁻¹ := by group
      _ = u * (y * (s' * t')) * u⁻¹ := this
      _ = (u * y * u⁻¹) * (u * s' * u⁻¹) * (u * t' * u⁻¹) := by group
      _ = y⁻¹ * (s' * t'⁻¹) := by rw [huy, hus', hut']; group
  have h1 : t' = s'⁻¹ * y⁻¹ * s * t := by
    calc t' = s'⁻¹ * (y⁻¹ * (y * (s' * t'))) := by group
      _ = s'⁻¹ * (y⁻¹ * (s * t)) := by rw [E0]
      _ = s'⁻¹ * y⁻¹ * s * t := by group
  have h2 : t' = t * s⁻¹ * y⁻¹ * s' := by
    have e : t * s⁻¹ = t' * s'⁻¹ * y := by
      calc t * s⁻¹ = (s * t⁻¹)⁻¹ := by group
        _ = (y⁻¹ * (s' * t'⁻¹))⁻¹ := by rw [Eu]
        _ = t' * s'⁻¹ * y := by group
    calc t' = (t' * s'⁻¹ * y) * y⁻¹ * s' := by group
      _ = (t * s⁻¹) * y⁻¹ * s' := by rw [← e]
      _ = t * s⁻¹ * y⁻¹ * s' := by group
  have hA : s'⁻¹ * y⁻¹ * s * t = t * s⁻¹ * y⁻¹ * s' := by rw [← h1, ← h2]
  have hB : y⁻¹ * (s'⁻¹ * s * t) = y⁻¹ * (t * s⁻¹ * s') := by
    have c1 : s'⁻¹ * y⁻¹ = y⁻¹ * s'⁻¹ := hcent _ ((R₂ N p).inv_mem hs'R) _ hyinv
    have c2 : s⁻¹ * y⁻¹ = y⁻¹ * s⁻¹ := hcent _ ((R₂ N p).inv_mem hsR) _ hyinv
    have c3 : t * y⁻¹ = y⁻¹ * t := hcent _ htR _ hyinv
    calc y⁻¹ * (s'⁻¹ * s * t) = (y⁻¹ * s'⁻¹) * s * t := by group
      _ = (s'⁻¹ * y⁻¹) * s * t := by rw [c1]
      _ = t * s⁻¹ * y⁻¹ * s' := hA
      _ = t * (s⁻¹ * y⁻¹) * s' := by group
      _ = t * (y⁻¹ * s⁻¹) * s' := by rw [c2]
      _ = (t * y⁻¹) * s⁻¹ * s' := by group
      _ = (y⁻¹ * t) * s⁻¹ * s' := by rw [c3]
      _ = y⁻¹ * (t * s⁻¹ * s') := by group
  have hC : (s'⁻¹ * s) * t = t * (s'⁻¹ * s)⁻¹ := by
    have := mul_left_cancel hB
    calc (s'⁻¹ * s) * t = s'⁻¹ * s * t := by group
      _ = t * s⁻¹ * s' := this
      _ = t * (s'⁻¹ * s)⁻¹ := by group
  set c := s'⁻¹ * s with hc
  have hcA : c ∈ RA N p u := (RA N p u).mul_mem ((RA N p u).inv_mem hs') hs
  have hzc : N.z * c * N.z⁻¹ = c⁻¹ := (RA_inv h).1 c hcA
  have hzt := (t9_RB_inv h).1 t ht
  have hD : c⁻¹ * t⁻¹ = t⁻¹ * c := by
    have := congrArg (fun g => N.z * g * N.z⁻¹) hC
    calc c⁻¹ * t⁻¹ = (N.z * c * N.z⁻¹) * (N.z * t * N.z⁻¹) := by rw [hzc, hzt]
      _ = N.z * (c * t) * N.z⁻¹ := by group
      _ = N.z * (t * c⁻¹) * N.z⁻¹ := this
      _ = (N.z * t * N.z⁻¹) * (N.z * c⁻¹ * N.z⁻¹) := by group
      _ = t⁻¹ * c := by
        rw [hzt]
        have : N.z * c⁻¹ * N.z⁻¹ = (N.z * c * N.z⁻¹)⁻¹ := by group
        rw [this, hzc]; group
  have hr1 : t * c = c⁻¹ * t := by
    have h0 : t * c⁻¹ * t⁻¹ = c := by
      calc t * c⁻¹ * t⁻¹ = t * (c⁻¹ * t⁻¹) := by group
        _ = t * (t⁻¹ * c) := by rw [hD]
        _ = c := by group
    calc t * c = (t * c⁻¹ * t⁻¹)⁻¹ * t := by group
      _ = c⁻¹ * t := by rw [h0]
  have hr2 : c * t = t * c⁻¹ := hC
  have hcomm : Commute (t * t) c := by
    show t * t * c = c * (t * t)
    calc t * t * c = t * (t * c) := by group
      _ = t * (c⁻¹ * t) := by rw [hr1]
      _ = (t * c⁻¹) * t := by group
      _ = (c * t) * t := by rw [hr2]
      _ = c * (t * t) := by group
  have hodd_t : Odd (orderOf t) := t6_odd_of_pGroup h.prime h.p_ne_two hpg htR
  obtain ⟨k, hk⟩ := hodd_t
  have htt : (t * t) ^ (k + 1) = t := by
    have e : (t * t) ^ (k + 1) = t ^ (2 * k + 1) * t := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
    rw [e, ← hk, pow_orderOf_eq_one, one_mul]
  have hcomm' : Commute t c := by
    have := hcomm.pow_left (k + 1)
    rwa [htt] at this
  have hcc : c * c = 1 := by
    have h3 : c * t = t * c := hcomm'.symm.eq
    have h4 : c * t = c⁻¹ * t := by rw [h3, hr1]
    have h5 : c = c⁻¹ := mul_right_cancel h4
    calc c * c = c * c⁻¹ := by rw [← h5]
      _ = 1 := by group
  have hc1 : c = 1 := by
    have hodd := t6_odd_of_pGroup h.prime h.p_ne_two (RA_pGroup h) hcA
    have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcc)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h4 | h4
    · exact orderOf_eq_one_iff.1 h4
    · rw [h4] at hodd; exact absurd hodd (by decide)
  have hss : s = s' := by
    have : s'⁻¹ * s = 1 := hc1
    calc s = s' * (s'⁻¹ * s) := by group
      _ = s' := by rw [this, mul_one]
  subst hss
  have hty : t = y * t' := by
    have hsy : s * y = y * s := hcent s hsR y hyX
    have : s * t = s * (y * t') := by
      calc s * t = y * (s * t') := E0
        _ = (y * s) * t' := by group
        _ = (s * y) * t' := by rw [hsy]
        _ = s * (y * t') := by group
    exact mul_left_cancel this
  have hyRB : y ∈ RB N p u := by
    have : y = t * t'⁻¹ := by rw [hty]; group
    rw [this]
    exact (RB N p u).mul_mem ht ((RB N p u).inv_mem ht')
  have hy1 : y = 1 := t9_X₂_zu_fix h hyX (Subgroup.mem_centralizer_singleton_iff.1 hyRB.2)
  refine ⟨?_, rfl, ?_⟩
  · have h1' : x⁻¹ * x' = 1 := hy1
    exact inv_mul_eq_one.1 h1'
  · rw [hty, hy1, one_mul]

theorem t9_R₂_decomp {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) :
    ∀ r ∈ R₂ N p, ∃ x ∈ N.X₂, ∃ s ∈ RA N p u, ∃ t ∈ RB N p u, r = x * s * t := by
  let f : ↥N.X₂ × ↥(RA N p u) × ↥(RB N p u) → G := fun q => (q.1 : G) * (q.2.1 : G) * (q.2.2 : G)
  have hinj : Function.Injective f := by
    rintro ⟨⟨x, hx⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ ⟨⟨x', hx'⟩, ⟨s', hs'⟩, ⟨t', ht'⟩⟩ heq
    obtain ⟨h1, h2, h3⟩ := t9_prod_inj h hx hx' hs hs' ht ht' heq
    subst h1 h2 h3
    rfl
  have hsub : Set.range f ⊆ (R₂ N p : Set G) := by
    rintro _ ⟨⟨⟨x, hx⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩, rfl⟩
    exact (R₂ N p).mul_mem ((R₂ N p).mul_mem (X₂_le_R₂ h hx) hs.1) ht.1
  have hcard : Nat.card (Set.range f) = Nat.card ↥(R₂ N p) := by
    rw [← Nat.card_congr (Equiv.ofInjective f hinj), Nat.card_prod, Nat.card_prod, R₂_card_eq h,
      h.sec5.loc.card_X₂]
    ring
  have hfin : (R₂ N p : Set G).Finite := Set.toFinite _
  have heq : Set.range f = (R₂ N p : Set G) := by
    apply Set.eq_of_subset_of_ncard_le hsub _ hfin
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact le_of_eq (by simpa using hcard.symm)
  intro r hr
  have : r ∈ Set.range f := heq ▸ hr
  obtain ⟨⟨⟨x, hx⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩, hrf⟩ := this
  exact ⟨x, hx, s, hs, t, ht, hrf.symm⟩

omit [Finite G] in
theorem t9_conjBy_mono (g : G) {A B : Subgroup G} (hAB : A ≤ B) :
    BNPair.conjBy g A ≤ BNPair.conjBy g B := Subgroup.map_mono hAB

theorem t9_A_le {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) (a : Bool) :
    (if a then N.X₁' else N.X₁) ≤ N.K₁ := by
  cases a
  · simp only [Bool.false_eq_true, ite_false]
    rw [h.sec5.loc.K₁_eq]; exact le_sup_left
  · simp only [ite_true]
    rw [h.sec5.loc.K₁_eq]; exact le_sup_right

theorem t9_B_le {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) (b : Bool) :
    (if b then N.X₂' else N.X₂) ≤ N.K₂ := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [h.sec5.loc.K₂_eq]; exact le_sup_left
  · simp only [ite_true]
    rw [h.sec5.loc.K₂_eq]; exact le_sup_right

omit [Finite G] in
theorem t9_set_mul_sub {P : Subgroup G} {S T : Set G} (hS : S ⊆ P) (hT : T ⊆ P) :
    S * T ⊆ (P : Set G) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact P.mul_mem (hS ha) (hT hb)

theorem t9_mem_conj_sup {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) (g : G) (a b : Bool) {x : G}
    (hx : x ∈ BNPair.conjBy g ((if a then N.X₁' else N.X₁) ⊔ (if b then N.X₂' else N.X₂))) :
    ∃ x₁ ∈ BNPair.conjBy g (if a then N.X₁' else N.X₁), ∃ x₂ ∈ BNPair.conjBy g (if b then N.X₂' else N.X₂),
      x = x₁ * x₂ := by
  rw [t9_mem_conjBy] at hx
  obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := (mem_sup_iff_of_comm (fun x hx y hy =>
    h.sec5.loc.K_comm x (t9_A_le h a hx) y (t9_B_le h b hy)) _).1 hx
  refine ⟨g⁻¹ * a₁ * g, ?_, g⁻¹ * b₁ * g, ?_, ?_⟩
  · rw [t9_mem_conjBy]
    have : g * (g⁻¹ * a₁ * g) * g⁻¹ = a₁ := by group
    rw [this]; exact ha₁
  · rw [t9_mem_conjBy]
    have : g * (g⁻¹ * b₁ * g) * g⁻¹ = b₁ := by group
    rw [this]; exact hb₁
  · have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, hab]; group

theorem t9_shape_set {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6)
    {α β γ δ : Bool}
    (hRA : RA N4.toT2N3 N4.p u = BNPair.conjBy N4.a
      ((if α then N4.X₁' else N4.X₁) ⊔ (if β then N4.X₂' else N4.X₂)))
    (hRB : RB N4.toT2N3 N4.p u = BNPair.conjBy (N4.a ^ 2)
      ((if γ then N4.X₁' else N4.X₁) ⊔ (if δ then N4.X₂' else N4.X₂))) :
    N4.toCh6.Shape α β γ δ := by
  have hRP : R₂ N4.toT2N3 N4.p ≤ N4.P := t9_R₂_le_P hS6
  have hRA_P : ∀ x ∈ RA N4.toT2N3 N4.p u, x ∈ N4.P := fun x hx => hRP hx.1
  have hRB_P : ∀ x ∈ RB N4.toT2N3 N4.p u, x ∈ N4.P := fun x hx => hRP hx.1
  show (N4.P : Set G) = (N4.X₁ : Set G) * (N4.X₂ : Set G) *
    (BNPair.conjBy N4.a (if α then N4.X₁' else N4.X₁) : Set G) *
    (BNPair.conjBy N4.a (if β then N4.X₂' else N4.X₂) : Set G) *
    (BNPair.conjBy (N4.a ^ 2) (if γ then N4.X₁' else N4.X₁) : Set G) *
    (BNPair.conjBy (N4.a ^ 2) (if δ then N4.X₂' else N4.X₂) : Set G)
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨r, hr, y, hy, rfl⟩ := t9_P_split h hS6 hx
    have hX₁K : N4.X₁ ≤ N4.K₁ := X₁_le_K₁ h
    have hr' : y⁻¹ * r * y ∈ R₂ N4.toT2N3 N4.p := by
      have h0 : y⁻¹ * r * y⁻¹⁻¹ ∈ R₂ N4.toT2N3 N4.p :=
        hS6.K₁_normR₂ y⁻¹ (N4.K₁.inv_mem (hX₁K hy)) r hr
      simpa using h0
    obtain ⟨x₂, hx₂, s, hs, t, ht, hdec⟩ := t9_R₂_decomp h _ hr'
    obtain ⟨s₁, hs₁, s₂, hs₂, hss⟩ := t9_mem_conj_sup h N4.a α β (hRA ▸ hs)
    obtain ⟨t₁, ht₁, t₂, ht₂, htt⟩ := t9_mem_conj_sup h (N4.a ^ 2) γ δ (hRB ▸ ht)
    have e : r * y = y * x₂ * s₁ * s₂ * t₁ * t₂ := by
      have h1 : r = y * (y⁻¹ * r * y) * y⁻¹ := by group
      calc r * y = y * (y⁻¹ * r * y) := by group
        _ = y * (x₂ * s * t) := by rw [hdec]
        _ = y * (x₂ * (s₁ * s₂) * (t₁ * t₂)) := by rw [hss, htt]
        _ = y * x₂ * s₁ * s₂ * t₁ * t₂ := by group
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul
      (Set.mul_mem_mul hy hx₂) hs₁) hs₂) ht₁) ht₂
  · apply t9_set_mul_sub (t9_set_mul_sub (t9_set_mul_sub (t9_set_mul_sub (t9_set_mul_sub ?_ ?_) ?_) ?_) ?_) ?_
    · exact fun x hx => t9_X₁_le_P hS6 hx
    · exact fun x hx => hRP (X₂_le_R₂ h hx)
    · intro x hx
      apply hRA_P
      rw [hRA]
      exact t9_conjBy_mono _ le_sup_left hx
    · intro x hx
      apply hRA_P
      rw [hRA]
      exact t9_conjBy_mono _ le_sup_right hx
    · intro x hx
      apply hRB_P
      rw [hRB]
      exact t9_conjBy_mono _ le_sup_left hx
    · intro x hx
      apply hRB_P
      rw [hRB]
      exact t9_conjBy_mono _ le_sup_right hx

theorem t9_cent_z {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) :
    Subgroup.centralizer {N4.toT2N3.z} ⊓ N4.P = N4.X₁ ⊔ N4.X₂ := by
  have hX₁K : N4.X₁ ≤ N4.K₁ := X₁_le_K₁ h
  have hX₂K : N4.X₂ ≤ N4.K₂ := by rw [h.sec5.loc.K₂_eq]; exact le_sup_left
  have hzK : ∀ k ∈ N4.K₁ ⊔ N4.K₂, k * N4.toT2N3.z = N4.toT2N3.z * k := h.zK
  apply le_antisymm
  · rintro x ⟨hxz, hxP⟩
    have hxz' : x * N4.toT2N3.z = N4.toT2N3.z * x := (Subgroup.mem_centralizer_singleton_iff.1 hxz)
    obtain ⟨r, hr, y, hy, rfl⟩ := t9_P_split h hS6 hxP
    have hyz : y * N4.toT2N3.z = N4.toT2N3.z * y := hzK y (Subgroup.mem_sup_left (hX₁K hy))
    have hrz : N4.toT2N3.z * r * N4.toT2N3.z⁻¹ = r := by
      have e : N4.toT2N3.z * (r * y) * N4.toT2N3.z⁻¹ = r * y := by
        calc N4.toT2N3.z * (r * y) * N4.toT2N3.z⁻¹ = (r * y) * N4.toT2N3.z * N4.toT2N3.z⁻¹ := by
              rw [← hxz']
          _ = r * y := by group
      have e2 : N4.toT2N3.z * y * N4.toT2N3.z⁻¹ = y := by
        calc N4.toT2N3.z * y * N4.toT2N3.z⁻¹ = (y * N4.toT2N3.z) * N4.toT2N3.z⁻¹ := by rw [hyz]
          _ = y := by group
      calc N4.toT2N3.z * r * N4.toT2N3.z⁻¹
          = (N4.toT2N3.z * (r * y) * N4.toT2N3.z⁻¹) * (N4.toT2N3.z * y * N4.toT2N3.z⁻¹)⁻¹ := by group
        _ = r := by rw [e, e2]; group
    have hrX : r ∈ N4.X₂ := R₂_Cz h r hr hrz
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hrX) (Subgroup.mem_sup_left hy)
  · apply le_inf
    · apply sup_le
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.2 (hzK x (Subgroup.mem_sup_left (hX₁K hx)))
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.2 (hzK x (Subgroup.mem_sup_right (hX₂K hx)))
    · exact sup_le (t9_X₁_le_P hS6) ((X₂_le_R₂ h).trans (t9_R₂_le_P hS6))

theorem t9_cent_u {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) :
    Subgroup.centralizer {u} ⊓ N4.P = RA N4.toT2N3 N4.p u :=
  t9_cent_P h hS6 (u_mem_M₂ h) (h.sec5.loc.u_inv_X₁)

theorem t9_cent_zu {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) :
    Subgroup.centralizer {N4.toT2N3.z * u} ⊓ N4.P = RB N4.toT2N3 N4.p u := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have hvM : N4.toT2N3.z * u ∈ M₂ N4.toT2N3 := (M₂ N4.toT2N3).mul_mem (z_mem_M₂ h) (u_mem_M₂ h)
  refine t9_cent_P h hS6 hvM ?_
  intro y hy
  have hyz : y * N4.toT2N3.z = N4.toT2N3.z * y :=
    h.zK y (Subgroup.mem_sup_left (X₁_le_K₁ h hy))
  calc N4.toT2N3.z * u * y * (N4.toT2N3.z * u)⁻¹
      = N4.toT2N3.z * (u * y * u⁻¹) * N4.toT2N3.z⁻¹ := by group
    _ = N4.toT2N3.z * y⁻¹ * N4.toT2N3.z⁻¹ := by rw [h.sec5.loc.u_inv_X₁ y hy]
    _ = (N4.toT2N3.z * y * N4.toT2N3.z⁻¹)⁻¹ := by group
    _ = y⁻¹ := by
      have : N4.toT2N3.z * y * N4.toT2N3.z⁻¹ = y := by
        calc N4.toT2N3.z * y * N4.toT2N3.z⁻¹ = (y * N4.toT2N3.z) * N4.toT2N3.z⁻¹ := by rw [hyz]
          _ = y := by group
      rw [this]


end CFSG.GH74.GLS.Stage4.Rest.T9
