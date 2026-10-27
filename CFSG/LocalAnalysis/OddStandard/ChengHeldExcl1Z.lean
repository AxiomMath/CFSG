module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupZStar
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Conj
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2UniqW

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Datum.cj_mul_of_mem_Q (d : Datum A) {y x a : G} (hy : y ∈ d.X) (hx : x ∈ d.Q)
    (ha : a ∈ d.S) : cj a (y * x) = cj a y := by
  have h1 : y⁻¹ * a * y ∈ d.S := d.conj_inv_mem_S hy a ha
  have h2 : (y⁻¹ * a * y) * x = x * (y⁻¹ * a * y) := d.comm_Q_S hx h1
  unfold cj
  calc (y * x)⁻¹ * a * (y * x) = x⁻¹ * ((y⁻¹ * a * y) * x) := by group
    _ = x⁻¹ * (x * (y⁻¹ * a * y)) := by rw [h2]
    _ = y⁻¹ * a * y := by group

theorem Chart4.act_mul_of_mem_Q (c : Chart4 d α) (k : Kind) {y x : G} (hy : y ∈ d.X)
    (hx : x ∈ d.Q) (h : k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) :
    k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi (y * x) := by
  have e : ∀ a ∈ d.S, cj a (y * x) = cj a y := fun a ha => d.cj_mul_of_mem_Q hy hx ha
  have ht := e _ c.t_mem.2
  have hpi := e _ c.mem.1
  have htau := e _ c.mem.2.1
  have hmu := e _ c.mem.2.2.1
  have hlam := e _ c.mem.2.2.2.1
  have hze := e _ c.mem.2.2.2.2.1
  have hxi := e _ c.mem.2.2.2.2.2
  cases k <;> by_cases hα : α = 0 <;> simp only [Kind.Act, hα, ↓reduceIte] at h ⊢ <;>
    simp only [ht, hpi, htau, hmu, hlam, hze, hxi] <;> exact h

theorem Chart4.exists_rep_of_kinds (c : Chart4 d α) {k : Kind}
    (hk : ∀ k', (c.rep k').isSome → k' = k) {x : G} (hx : x ∈ d.X) (hxQS : x ∉ d.QS) :
    ∃ y, c.rep k = some y ∧ ∃ u ∈ d.QS, x = u * y := by
  obtain ⟨k', y, hrep, u, hu, rfl⟩ := c.cover x hx hxQS
  have hk' : k' = k := hk k' (by rw [hrep]; rfl)
  subst hk'
  exact ⟨y, hrep, u, hu, rfl⟩

theorem Chart4.mul_mem_QS_of_kinds
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    {k : Kind} (hk : ∀ k', (c.rep k').isSome → k' = k) {a b : G} (ha : a ∈ d.X)
    (haQS : a ∉ d.QS) (hb : b ∈ d.X) (hbQS : b ∉ d.QS) : a * b ∈ d.QS := by
  obtain ⟨y, hy, u₁, hu₁, rfl⟩ := c.exists_rep_of_kinds hk ha haQS
  obtain ⟨y', hy', u₂, hu₂, rfl⟩ := c.exists_rep_of_kinds hk hb hbQS
  obtain rfl : y = y' := Option.some_injective _ (hy.symm.trans hy')
  obtain ⟨hyX, -, -⟩ := c.rep_mem k y hy
  have e : u₁ * y * (u₂ * y) = u₁ * (y * u₂ * y⁻¹) * (y * y) := by group
  rw [e]
  exact mul_mem (mul_mem hu₁ (d.conj_mem_QS hyX hu₂)) (c.sq_mem_QS hα h hP hQ hyX)

theorem Datum.exists_conj_involution (d : Datum A) (h : Hyp G A) :
    ∃ i ∈ d.X, i * i = 1 ∧ i ≠ 1 ∧ i ≠ d.q ∧ IsConj d.q i := by
  obtain ⟨g₀, hgX, hgne⟩ := d.exists_conj_ne h
  have hqq : d.q * d.q = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by simp [d.q_ord])
  refine ⟨g₀⁻¹ * d.q * g₀, hgX, ?_, fun h1 => ?_, hgne, isConj_iff.2 ⟨g₀⁻¹, by group⟩⟩
  · calc (g₀⁻¹ * d.q * g₀) * (g₀⁻¹ * d.q * g₀) = g₀⁻¹ * (d.q * d.q) * g₀ := by group
      _ = 1 := by rw [hqq]; group
  · have hq1 : d.q = 1 := by
      have h2 : g₀⁻¹ * d.q * g₀ = g₀⁻¹ * 1 * g₀ := by rw [h1]; group
      exact mul_left_cancel (mul_right_cancel h2)
    have hord := d.q_ord
    rw [hq1, orderOf_one] at hord
    omega

theorem Chart4.exists_z
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {k : Kind}
    (hk : ∀ k', (c.rep k').isSome → k' = k) (hnc : ¬ IsConj d.q c.pi) :
    ∃ z, z ∈ d.X ∧ z ∉ d.QS ∧ z * z = 1 ∧ IsConj d.q z ∧
      k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi z := by
  obtain ⟨i, hiX, hi2, hi1, hiq, hqi⟩ := d.exists_conj_involution h
  by_cases hiQS : i ∈ d.QS
  · exact absurd (hqi.trans (c.involution_QS_conj_pi hα h hP hQ hc hiQS hi2 hi1 hiq)) hnc
  · obtain ⟨y, hy, u, hu, hiu⟩ := c.exists_rep_of_kinds hk hiX hiQS
    obtain ⟨hyX, hyQS, hact⟩ := c.rep_mem k y hy
    obtain ⟨s, hs, x, hx, hz⟩ :=
      c.act_of_involution hα h hP hQ hS2 hc k hyX hact hi2 ⟨u, hu, hiu⟩
    have hz' : s⁻¹ * i * s = y * x := hz
    refine ⟨y * x, d.X.mul_mem hyX (d.Q_le_X hx), fun hmem => hyQS ?_, ?_, ?_,
      c.act_mul_of_mem_Q k hyX hx hact⟩
    · have := d.QS.mul_mem hmem (d.QS.inv_mem (mem_sup_left hx : x ∈ d.QS))
      simpa using this
    · rw [← hz']
      calc s⁻¹ * i * s * (s⁻¹ * i * s) = s⁻¹ * (i * i) * s := by group
        _ = 1 := by rw [hi2]; group
    · refine hqi.trans (isConj_iff.2 ⟨s⁻¹, ?_⟩)
      rw [← hz']
      group

theorem Datum.conj_QS_on_S (d : Datum A) {u s a : G} (hu : u ∈ d.Q) (hs : s ∈ d.S)
    (ha : a ∈ d.S) : (u * s) * a * (u * s)⁻¹ = s * a * s⁻¹ := by
  have h1 : s * a * s⁻¹ ∈ d.S := d.S.mul_mem (d.S.mul_mem hs ha) (d.S.inv_mem hs)
  have h2 := d.comm_Q_S hu h1
  calc (u * s) * a * (u * s)⁻¹ = u * (s * a * s⁻¹) * u⁻¹ := by group
    _ = s * a * s⁻¹ := by rw [← h2]; group

end CFSG.OddStandard.ChengHeld
