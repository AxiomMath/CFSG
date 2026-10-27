module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B0b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}

@[expose] def y6Um (A V : Subgroup G) (z t : G) : Set G :=
  {x | ∃ a ∈ A, a ^ 2 = z ∧ ∃ v ∈ V, x = a * t * v}

@[expose] def y6Up (A V : Subgroup G) (t : G) : Set G :=
  {x | ∃ a ∈ A, a ^ 2 = 1 ∧ ∃ v ∈ V, x = a * t * v}

private lemma y6_conj_t_eq_inv (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {v : G} (hv : v ∈ V) :
    t * v * t⁻¹ = v⁻¹ := by
  have hvu : v ∈ zpowers u := by simpa [h.hV] using hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvu
  rw [← hk, ← conj_zpow, h.t_inv, inv_zpow]

private lemma y6_comm_A_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {a v : G} (ha : a ∈ A)
    (hv : v ∈ V) : a * v = v * a := by
  have hvu : v ∈ zpowers u := by simpa [h.hV] using hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvu
  have hcu : Commute a u := h.u_cent a ha
  rw [← hk]
  exact (hcu.zpow_right k).eq

private lemma y6_pow_mem_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) (i : ℕ) : u ^ i ∈ V := by
  rw [h.hV]
  exact Subgroup.npow_mem_zpowers u i

private lemma y6_pow_mul_t (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) (i : ℕ) :
    u ^ i * t = t * (u ^ i)⁻¹ := by
  have h2 : t * u ^ i = (u ^ i)⁻¹ * t := by
    have h1 : t * u ^ i * t⁻¹ = (u ^ i)⁻¹ := by
      rw [← conj_pow, h.t_inv, inv_pow]
    calc t * u ^ i = t * u ^ i * (t⁻¹ * t) := by group
      _ = (t * u ^ i * t⁻¹) * t := by group
      _ = (u ^ i)⁻¹ * t := by rw [h1]
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← h.t_ord]
    exact pow_orderOf_eq_one t
  calc u ^ i * t = (t * t) * (u ^ i * t) := by rw [ht2, one_mul]
    _ = t * (t * u ^ i) * t := by group
    _ = t * ((u ^ i)⁻¹ * t) * t := by rw [h2]
    _ = t * (u ^ i)⁻¹ * (t * t) := by group
    _ = t * (u ^ i)⁻¹ := by rw [ht2, mul_one]

private lemma y6_sq_atv (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {a v : G} (ha : a ∈ A)
    (hv : v ∈ V) : (a * t * v) ^ 2 = a ^ 2 := by
  have hta : t * a = a * t := (h.t_cent a ha).symm
  have hva : v * a = a * v := (y6_comm_A_V h ha hv).symm
  have htv : t * v * t = v⁻¹ := by
    simpa [inv_eq_self_of_orderOf_eq_two h.t_ord] using y6_conj_t_eq_inv h hv
  have htv2 : t * v * t * v = 1 := by
    rw [show t * v * t * v = (t * v * t) * v by group, htv, inv_mul_cancel]
  rw [pow_two]
  calc (a * t * v) * (a * t * v) = a * t * (v * a) * t * v := by group
    _ = a * t * (a * v) * t * v := by rw [hva]
    _ = a * (t * a) * v * t * v := by group
    _ = a * (a * t) * v * t * v := by rw [hta]
    _ = a * a * (t * v * t * v) := by group
    _ = a * a * 1 := by rw [htv2]
    _ = a ^ 2 := by rw [pow_two, mul_one]

theorem y6_sq_Um (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : ∀ x ∈ y6Um A V z t, x ^ 2 = z := by
  rintro x ⟨a, ha, haz, v, hv, rfl⟩
  rw [y6_sq_atv h ha hv, haz]

theorem y6_sq_Up (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : ∀ x ∈ y6Up A V t, x ^ 2 = 1 := by
  rintro x ⟨a, ha, ha1, v, hv, rfl⟩
  rw [y6_sq_atv h ha hv, ha1]

theorem y6_Um_sub (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ x ∈ y6Um A V z t, x ∈ A ⊔ C0 ∧ x ∉ A ⊔ V := by
  rintro x ⟨a, ha, -, v, hv, rfl⟩
  refine ⟨mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right (y6_t_mem_C0 h)))
    (mem_sup_right (y6_V_le_C0 h hv)), ?_⟩
  intro hx
  exact y6_t_not_mem_AV h (by
    have ht : t = a⁻¹ * (a * t * v) * v⁻¹ := by group
    rw [ht]
    exact mul_mem (mul_mem (mem_sup_left (inv_mem ha)) hx) (mem_sup_right (inv_mem hv)))

theorem y6_Up_sub (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ x ∈ y6Up A V t, x ∈ A ⊔ C0 ∧ x ∉ A ⊔ V := by
  rintro x ⟨a, ha, -, v, hv, rfl⟩
  refine ⟨mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right (y6_t_mem_C0 h)))
    (mem_sup_right (y6_V_le_C0 h hv)), ?_⟩
  intro hx
  exact y6_t_not_mem_AV h (by
    have ht : t = a⁻¹ * (a * t * v) * v⁻¹ := by group
    rw [ht]
    exact mul_mem (mul_mem (mem_sup_left (inv_mem ha)) hx) (mem_sup_right (inv_mem hv)))

theorem y6_C1_split (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ x ∈ A ⊔ C0, x ∈ A ⊔ V ∨ x ∈ y6Um A V z t ∨ x ∈ y6Up A V t := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := y6_C1_elems h x hx
  have hc' : c ∈ (closure ({u, t} : Set G) : Subgroup G) := by simpa [h.hC0] using hc
  obtain ⟨i, hi | hi⟩ := y6_d8_elems h.u_ord h.t_ord h.t_inv c hc'
  · left
    rw [hi]
    exact mul_mem (mem_sup_left ha) (mem_sup_right (y6_pow_mem_V h i))
  · rcases y6q8_sq_cases h.rel a (by simpa [h.hA] using ha) with ha1 | haz
    · right; right
      rw [hi]
      refine ⟨a, ha, ha1, (u ^ i)⁻¹, inv_mem (y6_pow_mem_V h i), ?_⟩
      rw [y6_pow_mul_t h i, mul_assoc]
    · right; left
      rw [hi]
      refine ⟨a, ha, haz, (u ^ i)⁻¹, inv_mem (y6_pow_mem_V h i), ?_⟩
      rw [y6_pow_mul_t h i, mul_assoc]

theorem y6_mem_Um_iff (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ x : G, x ∈ y6Um A V z t ↔ x ∈ A ⊔ C0 ∧ x ∉ A ⊔ V ∧ x ^ 2 = z := by
  intro x
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := y6_Um_sub h x hx
    exact ⟨hx1, hx2, y6_sq_Um h x hx⟩
  · rintro ⟨hx1, hx2, hx3⟩
    rcases y6_C1_split h x hx1 with hAV | hUm | hUp
    · exact absurd hAV hx2
    · exact hUm
    · exfalso
      have h1 := y6_sq_Up h x hUp
      rw [hx3] at h1
      exact h.z_ne h1

theorem y6_Um_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ x ∈ y6Um A V z t, ∀ v ∈ V, x * v ∈ y6Um A V z t := by
  rintro x ⟨a, ha, haz, v₀, hv₀, rfl⟩ v hv
  exact ⟨a, ha, haz, v₀ * v, mul_mem hv₀ hv, by group⟩

theorem y6_Up_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ x ∈ y6Up A V t, ∀ v ∈ V, x * v ∈ y6Up A V t := by
  rintro x ⟨a, ha, ha1, v₀, hv₀, rfl⟩ v hv
  exact ⟨a, ha, ha1, v₀ * v, mul_mem hv₀ hv, by group⟩

end CFSG.OddStandard.HigherRank.YamadaG23
