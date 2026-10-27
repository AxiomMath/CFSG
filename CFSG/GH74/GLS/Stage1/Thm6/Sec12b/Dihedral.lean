module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup

variable {G : Type*} [Group G]

structure DihData (D : Subgroup G) (ρ s : G) (j : ℕ) : Prop where
  ρ_mem : ρ ∈ D
  s_mem : s ∈ D
  s_sq : s * s = 1
  s_conj : s * ρ * s⁻¹ = ρ⁻¹
  elem : ∀ d ∈ D, ∃ i : ℤ, d = ρ ^ i ∨ d = s * ρ ^ i
  ord : orderOf ρ = 4 * 2 ^ j

theorem cs_lemma' {ρ s b : G} (hb2 : b * b = 1) {c : ℤ}
    (hs : b * s * b⁻¹ = s * ρ ^ c) : ρ ^ c * (b * ρ * b⁻¹) ^ c = 1 := by
  have h1 : b * (b * s * b⁻¹) * b⁻¹ = s := by
    calc b * (b * s * b⁻¹) * b⁻¹ = (b * b) * s * (b * b)⁻¹ := by group
      _ = s := by rw [hb2]; simp
  rw [hs] at h1
  have h2 : b * (s * ρ ^ c) * b⁻¹ = (s * ρ ^ c) * (b * ρ * b⁻¹) ^ c := by
    calc b * (s * ρ ^ c) * b⁻¹ = (b * s * b⁻¹) * (b * ρ ^ c * b⁻¹) := by group
      _ = (s * ρ ^ c) * (b * ρ * b⁻¹) ^ c := by rw [hs, conj_zpow]
  rw [h2] at h1
  have h3 : s * (ρ ^ c * (b * ρ * b⁻¹) ^ c) = s * 1 := by rw [mul_one, ← mul_assoc]; exact h1
  exact mul_left_cancel h3

namespace DihData

variable {D : Subgroup G} {ρ s : G} {j : ℕ}

theorem s_inv (h : DihData D ρ s j) : s⁻¹ = s := inv_eq_of_mul_eq_one_right h.s_sq

theorem zpow_eq_one_iff (h : DihData D ρ s j) (i : ℤ) :
    ρ ^ i = 1 ↔ ((4 * 2 ^ j : ℕ) : ℤ) ∣ i := by
  rw [← orderOf_dvd_iff_zpow_eq_one, h.ord]

theorem zpow_eq_iff (h : DihData D ρ s j) (i k : ℤ) :
    ρ ^ i = ρ ^ k ↔ ((4 * 2 ^ j : ℕ) : ℤ) ∣ (i - k) := by
  rw [← h.zpow_eq_one_iff, zpow_sub, mul_inv_eq_one]

theorem s_zpow (h : DihData D ρ s j) (i : ℤ) : s * ρ ^ i * s⁻¹ = ρ ^ (-i) := by
  rw [← conj_zpow, h.s_conj, inv_zpow, zpow_neg]

theorem zpow_s (h : DihData D ρ s j) (i : ℤ) : ρ ^ i * s = s * ρ ^ (-i) := by
  have := h.s_zpow (-i)
  rw [neg_neg] at this
  calc ρ ^ i * s = (s * ρ ^ (-i) * s⁻¹) * s := by rw [this]
    _ = s * ρ ^ (-i) := by group

theorem sr_sq (h : DihData D ρ s j) (i : ℤ) : (s * ρ ^ i) * (s * ρ ^ i) = 1 := by
  have h1 := h.s_zpow i
  calc (s * ρ ^ i) * (s * ρ ^ i) = (s * ρ ^ i * s⁻¹) * (s * s) * ρ ^ i := by group
    _ = 1 := by rw [h1, h.s_sq]; simp

@[expose] def zc (j : ℕ) : ℤ := 2 * 2 ^ j

theorem two_zc (j : ℕ) : 2 * zc j = ((4 * 2 ^ j : ℕ) : ℤ) := by
  unfold zc; push_cast; ring

theorem q_pos (j : ℕ) : (0 : ℤ) < 2 ^ j := by positivity

theorem z0_sq (h : DihData D ρ s j) : ρ ^ zc j * ρ ^ zc j = 1 := by
  rw [← zpow_add, ← two_mul, two_zc]
  exact (h.zpow_eq_one_iff _).2 dvd_rfl

theorem z0_ne_one (h : DihData D ρ s j) : ρ ^ zc j ≠ 1 := by
  rw [Ne, h.zpow_eq_one_iff]
  intro hd
  have h1 : (4 * 2 ^ j : ℤ) ∣ 2 * 2 ^ j := by
    have := hd
    unfold zc at this
    push_cast at this
    exact this
  have h2 := q_pos j
  have := Int.le_of_dvd (by positivity) h1
  nlinarith

theorem z0_inv (h : DihData D ρ s j) : ρ ^ (-zc j) = ρ ^ zc j := by
  rw [h.zpow_eq_iff]
  have : -zc j - zc j = -(2 * zc j) := by ring
  rw [this, two_zc]
  exact (dvd_neg).2 dvd_rfl

theorem z0_central (h : DihData D ρ s j) : ∀ d ∈ D, ρ ^ zc j * d = d * ρ ^ zc j := by
  intro d hd
  obtain ⟨i, rfl | rfl⟩ := h.elem d hd
  · rw [← zpow_add, ← zpow_add, add_comm]
  · calc ρ ^ zc j * (s * ρ ^ i) = (ρ ^ zc j * s) * ρ ^ i := by group
      _ = (s * ρ ^ (-zc j)) * ρ ^ i := by rw [h.zpow_s]
      _ = (s * ρ ^ zc j) * ρ ^ i := by rw [h.z0_inv]
      _ = s * ρ ^ i * ρ ^ zc j := by rw [mul_assoc, ← zpow_add, add_comm, zpow_add, mul_assoc]

theorem zpow_sq_cases (h : DihData D ρ s j) (i : ℤ) (hi : ρ ^ i * ρ ^ i = 1) :
    ρ ^ i = 1 ∨ ρ ^ i = ρ ^ zc j := by
  rw [← zpow_add, h.zpow_eq_one_iff] at hi
  obtain ⟨t, ht⟩ := hi
  push_cast at ht
  have hq := q_pos j
  have hi2 : i = 2 * 2 ^ j * t := by nlinarith
  obtain ⟨t', rfl | rfl⟩ := Int.even_or_odd' t
  · left
    rw [h.zpow_eq_one_iff]
    exact ⟨t', by push_cast; rw [hi2]; ring⟩
  · right
    rw [h.zpow_eq_iff]
    exact ⟨t', by push_cast; rw [hi2]; unfold zc; ring⟩

theorem ρ_sq_ne_one (h : DihData D ρ s j) : ρ * ρ ≠ 1 := by
  intro h1
  have : ρ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h1
  rw [h.zpow_eq_one_iff] at this
  have h1 : (4 * 2 ^ j : ℤ) ∣ 2 := by exact_mod_cast this
  have := Int.le_of_dvd (by norm_num) h1
  have hq := q_pos j
  nlinarith

theorem s_ne_one (h : DihData D ρ s j) : s ≠ 1 := by
  intro e
  have h1 := h.s_conj
  rw [e] at h1
  simp at h1
  apply h.ρ_sq_ne_one
  have : ρ * ρ = ρ⁻¹ * ρ := by rw [← h1]
  rw [this]; simp

theorem inv_cases (h : DihData D ρ s j) : ∀ d ∈ D, d * d = 1 →
    d = 1 ∨ d = ρ ^ zc j ∨ ∃ i : ℤ, d = s * ρ ^ i := by
  intro d hd hd2
  obtain ⟨i, rfl | rfl⟩ := h.elem d hd
  · rcases h.zpow_sq_cases i hd2 with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)

theorem prod_inv (h : DihData D ρ s j) : ∀ d ∈ D, ∃ c₁ ∈ D, ∃ c₂ ∈ D,
    c₁ * c₁ = 1 ∧ c₂ * c₂ = 1 ∧ d = c₁ * c₂ := by
  intro d hd
  obtain ⟨i, rfl | rfl⟩ := h.elem d hd
  · refine ⟨s, h.s_mem, s * ρ ^ i, D.mul_mem h.s_mem (D.zpow_mem h.ρ_mem i), h.s_sq, h.sr_sq i, ?_⟩
    rw [← mul_assoc, h.s_sq, one_mul]
  · exact ⟨s * ρ ^ i, hd, 1, D.one_mem, h.sr_sq i, by simp, by simp⟩

theorem central_inv_eq (h : DihData D ρ s j) {y : G} (hy : y ∈ D) (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hc : ∀ d ∈ D, y * d = d * y) : y = ρ ^ zc j := by
  rcases h.inv_cases y hy hy2 with e | e | ⟨i, e⟩
  · exact absurd e hy1
  · exact e
  · exfalso
    have h1 := hc ρ h.ρ_mem
    rw [e] at h1
    have h2 : ρ * (s * ρ ^ i) = s * ρ ^ (i - 1) := by
      calc ρ * (s * ρ ^ i) = (ρ ^ (1 : ℤ) * s) * ρ ^ i := by simp [mul_assoc]
        _ = (s * ρ ^ (-1 : ℤ)) * ρ ^ i := by rw [h.zpow_s]
        _ = s * ρ ^ (i - 1) := by rw [mul_assoc, ← zpow_add]; congr 2; ring
    have h3 : s * ρ ^ i * ρ = s * ρ ^ (i + 1) := by
      rw [mul_assoc, ← zpow_add_one]
    rw [h2, h3] at h1
    have h4 : ρ ^ (i + 1) = ρ ^ (i - 1) := mul_left_cancel h1
    rw [← mul_inv_eq_one, ← zpow_sub] at h4
    have h5 : (i + 1) - (i - 1) = 2 := by ring
    rw [h5, zpow_two] at h4
    exact h.ρ_sq_ne_one h4


theorem s_ne_z0 (h : DihData D ρ s j) : s ≠ ρ ^ zc j := by
  intro e
  have hc := h.z0_central ρ h.ρ_mem
  have h1 : s * ρ * s⁻¹ = ρ := by
    rw [e, hc]; group
  rw [h.s_conj] at h1
  apply h.ρ_sq_ne_one
  have : ρ * ρ = ρ⁻¹ * ρ := by rw [h1]
  rw [this]; simp

theorem act (h : DihData D ρ s j) {g : G} (hg : ∀ d, d ∈ D ↔ g * d * g⁻¹ ∈ D) :
    ∃ u c : ℤ, Odd u ∧ g * ρ * g⁻¹ = ρ ^ u ∧ g * s * g⁻¹ = s * ρ ^ c := by
  have hρ : g * ρ * g⁻¹ ∈ D := (hg ρ).1 h.ρ_mem
  obtain ⟨u, hu⟩ : ∃ u : ℤ, g * ρ * g⁻¹ = ρ ^ u := by
    obtain ⟨i, e | e⟩ := h.elem _ hρ
    · exact ⟨i, e⟩
    · exfalso
      have h2 := h.sr_sq i
      rw [← e] at h2
      have h3 : g * (ρ * ρ) * g⁻¹ = 1 := by
        calc g * (ρ * ρ) * g⁻¹ = (g * ρ * g⁻¹) * (g * ρ * g⁻¹) := by group
          _ = 1 := h2
      have h4 : ρ * ρ = 1 := by
        have := congrArg (fun y => g⁻¹ * y * g) h3
        simpa [mul_assoc] using this
      exact h.ρ_sq_ne_one h4
  have hodd : Odd u := by
    by_contra hne
    obtain ⟨v, hv⟩ := Int.not_odd_iff_even.1 hne
    apply h.z0_ne_one
    have h1 : g * ρ ^ zc j * g⁻¹ = 1 := by
      rw [← conj_zpow, hu, ← zpow_mul, h.zpow_eq_one_iff]
      exact ⟨v, by unfold zc; push_cast; rw [hv]; ring⟩
    have h2 := congrArg (fun y => g⁻¹ * y * g) h1
    simpa [mul_assoc] using h2
  have hs : g * s * g⁻¹ ∈ D := (hg s).1 h.s_mem
  obtain ⟨c, hc⟩ : ∃ c : ℤ, g * s * g⁻¹ = s * ρ ^ c := by
    obtain ⟨i, e | e⟩ := h.elem _ hs
    · exfalso
      have h1 : (g * s * g⁻¹) * (g * ρ * g⁻¹) * (g * s * g⁻¹)⁻¹ = (g * ρ * g⁻¹)⁻¹ := by
        calc _ = g * (s * ρ * s⁻¹) * g⁻¹ := by group
          _ = g * ρ⁻¹ * g⁻¹ := by rw [h.s_conj]
          _ = (g * ρ * g⁻¹)⁻¹ := by group
      rw [e, hu] at h1
      have h2 : ρ ^ u = (ρ ^ u)⁻¹ := by
        calc ρ ^ u = ρ ^ i * ρ ^ u * (ρ ^ i)⁻¹ := by
              rw [← zpow_add, add_comm, zpow_add]; group
          _ = (ρ ^ u)⁻¹ := h1
      have h3 : ρ ^ (u + u) = 1 := by
        rw [zpow_add]
        nth_rewrite 2 [h2]
        exact mul_inv_cancel _
      rw [h.zpow_eq_one_iff] at h3
      obtain ⟨t, ht⟩ := h3
      push_cast at ht
      obtain ⟨k, hk⟩ := hodd
      have : (4 : ℤ) * (2 ^ j * t) = 4 * k + 2 := by rw [hk] at ht; linarith
      generalize 2 ^ j * t = X at this
      omega
    · exact ⟨i, e⟩
  exact ⟨u, c, hodd, hu, hc⟩

theorem conj_comp {g k : G} {u₁ c₁ u₂ c₂ : ℤ}
    (hρ₁ : g * ρ * g⁻¹ = ρ ^ u₁) (hs₁ : g * s * g⁻¹ = s * ρ ^ c₁)
    (hρ₂ : k * ρ * k⁻¹ = ρ ^ u₂) (hs₂ : k * s * k⁻¹ = s * ρ ^ c₂) (i : ℤ) :
    (g * k) * ρ ^ i * (g * k)⁻¹ = ρ ^ (u₁ * u₂ * i) ∧
    (g * k) * (s * ρ ^ i) * (g * k)⁻¹ = s * ρ ^ (c₁ + u₁ * c₂ + u₁ * u₂ * i) := by
  have e1 : (g * k) * ρ ^ i * (g * k)⁻¹ = ρ ^ (u₁ * u₂ * i) := by
    calc (g * k) * ρ ^ i * (g * k)⁻¹ = g * (k * ρ ^ i * k⁻¹) * g⁻¹ := by group
      _ = g * (k * ρ * k⁻¹) ^ i * g⁻¹ := by rw [conj_zpow]
      _ = g * (ρ ^ u₂) ^ i * g⁻¹ := by rw [hρ₂]
      _ = (g * ρ * g⁻¹) ^ (u₂ * i) := by rw [← zpow_mul, conj_zpow]
      _ = ρ ^ (u₁ * (u₂ * i)) := by rw [hρ₁, ← zpow_mul]
      _ = ρ ^ (u₁ * u₂ * i) := by rw [mul_assoc]
  have e2 : (g * k) * s * (g * k)⁻¹ = s * ρ ^ (c₁ + u₁ * c₂) := by
    calc (g * k) * s * (g * k)⁻¹ = g * (k * s * k⁻¹) * g⁻¹ := by group
      _ = g * (s * ρ ^ c₂) * g⁻¹ := by rw [hs₂]
      _ = (g * s * g⁻¹) * (g * ρ ^ c₂ * g⁻¹) := by group
      _ = (s * ρ ^ c₁) * (g * ρ * g⁻¹) ^ c₂ := by rw [hs₁, conj_zpow]
      _ = (s * ρ ^ c₁) * ρ ^ (u₁ * c₂) := by rw [hρ₁, ← zpow_mul]
      _ = s * ρ ^ (c₁ + u₁ * c₂) := by rw [mul_assoc, ← zpow_add]
  refine ⟨e1, ?_⟩
  calc (g * k) * (s * ρ ^ i) * (g * k)⁻¹ =
        ((g * k) * s * (g * k)⁻¹) * ((g * k) * ρ ^ i * (g * k)⁻¹) := by group
    _ = s * ρ ^ (c₁ + u₁ * c₂ + u₁ * u₂ * i) := by
        rw [e1, e2, mul_assoc, ← zpow_add]

theorem inner_s (h : DihData D ρ s j) (e m : ℤ) :
    ρ ^ e * (s * ρ ^ m) * (ρ ^ e)⁻¹ = s * ρ ^ (m - 2 * e) := by
  calc ρ ^ e * (s * ρ ^ m) * (ρ ^ e)⁻¹ = (ρ ^ e * s) * ρ ^ m * ρ ^ (-e) := by group
    _ = (s * ρ ^ (-e)) * ρ ^ m * ρ ^ (-e) := by rw [h.zpow_s]
    _ = s * ρ ^ (m - 2 * e) := by
        rw [mul_assoc, mul_assoc, ← zpow_add, ← zpow_add]; congr 2; ring

theorem comm_inner (h : DihData D ρ s j) {g k : G} (hg : ∀ d, d ∈ D ↔ g * d * g⁻¹ ∈ D)
    (hk : ∀ d, d ∈ D ↔ k * d * k⁻¹ ∈ D) :
    ∃ d ∈ D, ∀ y ∈ D, (g * k * g⁻¹ * k⁻¹) * y * (g * k * g⁻¹ * k⁻¹)⁻¹ = d * y * d⁻¹ := by
  obtain ⟨u₁, c₁, ⟨a, ha⟩, hρ₁, hs₁⟩ := h.act hg
  obtain ⟨u₂, c₂, ⟨b, hb⟩, hρ₂, hs₂⟩ := h.act hk
  refine ⟨ρ ^ (b * c₁ - a * c₂), D.zpow_mem h.ρ_mem _, fun y hy => ?_⟩
  have hkg : ∀ d, d ∈ D ↔ (k * g) * d * (k * g)⁻¹ ∈ D := by
    intro d
    have : (k * g) * d * (k * g)⁻¹ = k * (g * d * g⁻¹) * k⁻¹ := by group
    rw [this, ← hk, ← hg]
  have hy' : (k * g)⁻¹ * y * (k * g) ∈ D := by
    rw [hkg]
    have : (k * g) * ((k * g)⁻¹ * y * (k * g)) * (k * g)⁻¹ = y := by group
    rw [this]; exact hy
  have key : ∀ y' ∈ D, (g * k) * y' * (g * k)⁻¹ =
      ρ ^ (b * c₁ - a * c₂) * ((k * g) * y' * (k * g)⁻¹) * (ρ ^ (b * c₁ - a * c₂))⁻¹ := by
    intro y' hy'D
    obtain ⟨i, rfl | rfl⟩ := h.elem y' hy'D
    · rw [(conj_comp hρ₁ hs₁ hρ₂ hs₂ i).1, (conj_comp hρ₂ hs₂ hρ₁ hs₁ i).1, mul_comm u₂ u₁]
      group
    · rw [(conj_comp hρ₁ hs₁ hρ₂ hs₂ i).2, (conj_comp hρ₂ hs₂ hρ₁ hs₁ i).2, h.inner_s]
      congr 2
      rw [ha, hb]
      ring
  have e : (g * k * g⁻¹ * k⁻¹) * y * (g * k * g⁻¹ * k⁻¹)⁻¹ =
      (g * k) * ((k * g)⁻¹ * y * (k * g)) * (g * k)⁻¹ := by group
  rw [e, key _ hy']
  have e2 : (k * g) * ((k * g)⁻¹ * y * (k * g)) * (k * g)⁻¹ = y := by group
  rw [e2]

theorem finish_s (h : DihData D ρ s j) {b : G} {c : ℤ}
    (hs : b * s * b⁻¹ = s * ρ ^ c) (hc : ρ ^ c * (b * ρ * b⁻¹) ^ c = 1)
    (hρ : (b * ρ * b⁻¹) ^ c = ρ ^ c) : (b * s * b⁻¹ = s ∨ b * s * b⁻¹ = s * ρ ^ zc j) := by
  rw [hρ] at hc
  rcases h.zpow_sq_cases c hc with e | e
  · left; rw [hs, e, mul_one]
  · right; rw [hs, e]

theorem exists_normalized_four_of_pairs (h : DihData D ρ s j) {b : G} (hb2 : b * b = 1)
    (hb : ∀ d, d ∈ D ↔ b * d * b⁻¹ ∈ D)
    (hY : ∀ d₁ ∈ D, ∀ d₂ ∈ D, b * d₁ * b⁻¹ = d₁ ∨ b * d₂ * b⁻¹ = d₂ ∨
      b * (d₁⁻¹ * d₂) * b⁻¹ = d₁⁻¹ * d₂) :
    ∃ c ∈ D, c * c = 1 ∧ c ≠ 1 ∧ c ≠ ρ ^ zc j ∧
      (b * c * b⁻¹ = c ∨ b * c * b⁻¹ = c * ρ ^ zc j) := by
  obtain ⟨u, c, hodd, hρ, hs⟩ := h.act hb
  rcases hY ρ h.ρ_mem s h.s_mem with e | e | e
  · refine ⟨s, h.s_mem, h.s_sq, h.s_ne_one, h.s_ne_z0, ?_⟩
    apply h.finish_s hs (cs_lemma' hb2 hs)
    rw [e]
  · exact ⟨s, h.s_mem, h.s_sq, h.s_ne_one, h.s_ne_z0, Or.inl e⟩
  · refine ⟨ρ⁻¹ * s, D.mul_mem (D.inv_mem h.ρ_mem) h.s_mem, ?_, ?_, ?_, Or.inl e⟩
    · have h1 : s * ρ⁻¹ * s⁻¹ = ρ := by
        calc s * ρ⁻¹ * s⁻¹ = (s * ρ * s⁻¹)⁻¹ := by group
          _ = ρ := by rw [h.s_conj, inv_inv]
      calc ρ⁻¹ * s * (ρ⁻¹ * s) = ρ⁻¹ * (s * ρ⁻¹ * s⁻¹) * (s * s) := by group
        _ = 1 := by rw [h1, h.s_sq]; simp
    · intro e1
      have : s = ρ := by
        have := congrArg (fun y => ρ * y) e1
        simpa using this
      apply h.ρ_sq_ne_one
      rw [← this]; exact h.s_sq
    · intro e1
      have hs' : s = ρ * ρ ^ zc j := by
        have := congrArg (fun y => ρ * y) e1
        simpa using this
      have hcomm := h.z0_central ρ h.ρ_mem
      have h1 : s * ρ * s⁻¹ = ρ := by
        rw [hs']
        calc ρ * ρ ^ zc j * ρ * (ρ * ρ ^ zc j)⁻¹
            = ρ * (ρ ^ zc j * ρ) * (ρ ^ zc j)⁻¹ * ρ⁻¹ := by group
          _ = ρ * (ρ * ρ ^ zc j) * (ρ ^ zc j)⁻¹ * ρ⁻¹ := by rw [hcomm]
          _ = ρ := by group
      rw [h.s_conj] at h1
      apply h.ρ_sq_ne_one
      have : ρ * ρ = ρ⁻¹ * ρ := by rw [h1]
      rw [this]; simp

theorem exists_normalized_four_of_order_four (h : DihData D ρ s j) {b : G} (hb2 : b * b = 1)
    (hb : ∀ d, d ∈ D ↔ b * d * b⁻¹ ∈ D) {p : G} (hp : p ∈ D) (hp2 : p * p = ρ ^ zc j)
    (hbp : b * p * b⁻¹ = p) :
    ∃ c ∈ D, c * c = 1 ∧ c ≠ 1 ∧ c ≠ ρ ^ zc j ∧
      (b * c * b⁻¹ = c ∨ b * c * b⁻¹ = c * ρ ^ zc j) := by
  obtain ⟨u, c, ⟨a, ha⟩, hρ, hs⟩ := h.act hb
  obtain ⟨i, rfl | rfl⟩ := h.elem p hp
  swap
  · exfalso
    rw [h.sr_sq] at hp2
    exact h.z0_ne_one hp2.symm
  have h1 : ρ ^ (i + i - zc j) = 1 := by
    rw [zpow_sub, zpow_add, hp2, mul_inv_cancel]
  rw [h.zpow_eq_one_iff] at h1
  obtain ⟨t, ht⟩ := h1
  push_cast at ht
  have hq := q_pos j
  have hi : i = 2 ^ j * (1 + 2 * t) := by unfold zc at ht; nlinarith
  have h2 : ρ ^ (u * i) = ρ ^ i := by
    have : b * ρ ^ i * b⁻¹ = ρ ^ i := hbp
    rw [← conj_zpow, hρ, ← zpow_mul] at this
    exact this
  rw [h.zpow_eq_iff] at h2
  obtain ⟨w, hw⟩ := h2
  push_cast at hw
  have h3 : 2 * w = a * (1 + 2 * t) := by
    have : (4 : ℤ) * 2 ^ j * w = 2 * a * 2 ^ j * (1 + 2 * t) := by
      rw [← hw, ha, hi]; ring
    have h4 : (2 * 2 ^ j : ℤ) * (2 * w) = (2 * 2 ^ j) * (a * (1 + 2 * t)) := by linarith
    exact mul_left_cancel₀ (by positivity) h4
  have hae : Even a := by
    have h5 : 2 * w = a + 2 * (a * t) := by rw [h3]; ring
    generalize a * t = X at h5
    exact ⟨w - X, by omega⟩
  obtain ⟨a', ha'⟩ := hae
  have h6 := cs_lemma' (ρ := ρ) hb2 hs
  rw [hρ, ← zpow_mul, ← zpow_add] at h6
  rw [h.zpow_eq_one_iff] at h6
  obtain ⟨w', hw'⟩ := h6
  push_cast at hw'
  have hu : 1 + u = 2 * (2 * a' + 1) := by rw [ha, ha']; ring
  have h7 : (2 : ℤ) ^ (j + 1) ∣ c * (2 * a' + 1) := by
    refine ⟨w', ?_⟩
    have : (2 : ℤ) * (c * (2 * a' + 1)) = 2 * (2 ^ (j + 1) * w') := by
      have e1 : c + u * c = c * (1 + u) := by ring
      rw [e1, hu] at hw'
      calc (2 : ℤ) * (c * (2 * a' + 1)) = c * (2 * (2 * a' + 1)) := by ring
        _ = 4 * 2 ^ j * w' := hw'
        _ = 2 * (2 ^ (j + 1) * w') := by ring
    exact mul_left_cancel₀ (by norm_num) this
  have hcop : IsCoprime ((2 : ℤ) ^ (j + 1)) (2 * a' + 1) := by
    have : IsCoprime (2 : ℤ) (2 * a' + 1) := ⟨-a', 1, by ring⟩
    exact IsCoprime.pow_left this
  have h8 : (2 : ℤ) ^ (j + 1) ∣ c := hcop.dvd_of_dvd_mul_right h7
  obtain ⟨c', hc'⟩ := h8
  have hρc : (b * ρ * b⁻¹) ^ c = ρ ^ c := by
    rw [hρ, ← zpow_mul, h.zpow_eq_iff]
    exact ⟨2 * a' * c', by push_cast; rw [ha, ha', hc']; ring⟩
  refine ⟨s, h.s_mem, h.s_sq, h.s_ne_one, h.s_ne_z0, ?_⟩
  exact h.finish_s hs (cs_lemma' hb2 hs) hρc

end DihData

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
