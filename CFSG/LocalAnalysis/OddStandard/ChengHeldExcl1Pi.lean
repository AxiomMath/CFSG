module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Xi
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Z
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Open

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cm_eq_one_iff)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.field_act_parts (c : Chart4 d α) {y : G}
    (h : Kind.field.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) :
    cj c.pi y = c.pi ∧ cj c.tau y = c.pi * c.tau ∧ (α = 0 → cj c.t y = c.t) ∧
      (α ≠ 0 → cj c.t y = c.t⁻¹) := by
  by_cases hα : α = 0
  · simp only [Kind.Act, hα, ↓reduceIte] at h
    exact ⟨h.2.1, h.2.2.1, fun _ => h.1, fun h' => absurd hα h'⟩
  · simp only [Kind.Act, hα, ↓reduceIte] at h
    exact ⟨h.2.1, h.2.2.1, fun h' => absurd h' hα, fun _ => h.1⟩

theorem Chart4.cj_pi_of_S (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) :
    ∀ s ∈ d.S, s⁻¹ * c.pi * s = c.pi ∨ s⁻¹ * c.pi * s = d.q * c.pi := by
  have hcen := c.t_comm hα h hP hQ
  have fr := c.frame
  obtain ⟨hqX, hqc⟩ := d.q_mem_X h
  have hqcomm : ∀ x ∈ d.X, x * d.q = d.q * x := fun x hx =>
    mem_centralizer_singleton_iff.1 (hqc hx)
  have hqq : d.q * d.q = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by simp [d.q_ord])
  have hcj : ∀ x : G, x * c.pi = c.pi * x → x⁻¹ * c.pi * x = c.pi := fun x hx => by
    calc x⁻¹ * c.pi * x = x⁻¹ * (c.pi * x) := by group
      _ = x⁻¹ * (x * c.pi) := by rw [hx]
      _ = c.pi := by group
  have hmu : cj c.pi c.mu = d.q * c.pi := by rw [fr.pi_mu, c.q_eq]
  have hlam : cj c.pi c.lam = d.q * c.pi := by rw [fr.pi_lam, c.q_eq]
  have hze : cj c.pi c.ze = d.q * c.pi := by rw [fr.pi_ze, c.q_eq]
  have hxi : cj c.pi c.xi = c.pi := fr.pi_xi
  have htau : c.pi * c.tau = c.tau * c.pi := (cm_eq_one_iff.1 fr.pi_tau).eq
  intro s hs
  rw [← c.gen] at hs
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (hcj _ (hcen _ c.mem.1).symm)
    · exact Or.inl (by group)
    · exact Or.inl (hcj _ htau.symm)
    · exact Or.inr hmu
    · exact Or.inr hlam
    · exact Or.inr hze
    · exact Or.inl hxi
  | one => exact Or.inl (by group)
  | mul a b ha hb iha ihb =>
    have hbq : b⁻¹ * d.q * b = d.q := by
      have := hqcomm b (d.S_le_X (by rw [← c.gen]; exact hb))
      calc b⁻¹ * d.q * b = b⁻¹ * (d.q * b) := by group
        _ = b⁻¹ * (b * d.q) := by rw [← this]
        _ = d.q := by group
    have e : (a * b)⁻¹ * c.pi * (a * b) = b⁻¹ * (a⁻¹ * c.pi * a) * b := by group
    rw [e]
    rcases iha with h1 | h1
    · rw [h1]; exact ihb
    · rw [h1]
      have e2 : b⁻¹ * (d.q * c.pi) * b = d.q * (b⁻¹ * c.pi * b) := by
        calc b⁻¹ * (d.q * c.pi) * b = (b⁻¹ * d.q * b) * (b⁻¹ * c.pi * b) := by group
          _ = d.q * (b⁻¹ * c.pi * b) := by rw [hbq]
      rw [e2]
      rcases ihb with h2 | h2
      · rw [h2]; exact Or.inr rfl
      · rw [h2]
        refine Or.inl ?_
        rw [← mul_assoc, hqq, one_mul]
  | inv a ha iha =>
    have haX : a ∈ d.X := d.S_le_X (by rw [← c.gen]; exact ha)
    have haq : a * d.q * a⁻¹ = d.q := by
      calc a * d.q * a⁻¹ = (d.q * a) * a⁻¹ := by rw [hqcomm a haX]
        _ = d.q := by group
    have e : a⁻¹⁻¹ * c.pi * a⁻¹ = a * c.pi * a⁻¹ := by group
    rw [e]
    rcases iha with h1 | h1
    · left
      calc a * c.pi * a⁻¹ = a * (a⁻¹ * c.pi * a) * a⁻¹ := by rw [h1]
        _ = c.pi := by group
    · right
      have h3 : c.pi = d.q * (a * c.pi * a⁻¹) := by
        calc c.pi = a * (a⁻¹ * c.pi * a) * a⁻¹ := by group
          _ = a * (d.q * c.pi) * a⁻¹ := by rw [h1]
          _ = (a * d.q * a⁻¹) * (a * c.pi * a⁻¹) := by group
          _ = d.q * (a * c.pi * a⁻¹) := by rw [haq]
      calc a * c.pi * a⁻¹ = (d.q * d.q) * (a * c.pi * a⁻¹) := by rw [hqq, one_mul]
        _ = d.q * (d.q * (a * c.pi * a⁻¹)) := by group
        _ = d.q * c.pi := by rw [← h3]


theorem Chart4.cj_pi_of_QS (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) :
    ∀ x ∈ d.QS, x⁻¹ * c.pi * x = c.pi ∨ x⁻¹ * c.pi * x = d.q * c.pi := by
  intro x hx
  obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 hx
  have hπu : c.pi * u = u * c.pi := d.comm_Q_S hu c.mem.1
  have e : (u * s)⁻¹ * c.pi * (u * s) = s⁻¹ * (u⁻¹ * c.pi * u) * s := by group
  have e2 : u⁻¹ * c.pi * u = c.pi := by
    calc u⁻¹ * c.pi * u = u⁻¹ * (c.pi * u) := by group
      _ = u⁻¹ * (u * c.pi) := by rw [hπu]
      _ = c.pi := by group
  rw [e, e2]
  exact c.cj_pi_of_S hα h hP hQ s hs

theorem Chart4.cj_pi_of_X (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) (hk : ∀ k', (c.rep k').isSome → k' = Kind.field) :
    ∀ x ∈ d.X, x⁻¹ * c.pi * x = c.pi ∨ x⁻¹ * c.pi * x = d.q * c.pi := by
  intro x hx
  by_cases hxQS : x ∈ d.QS
  · exact c.cj_pi_of_QS hα h hP hQ x hxQS
  · obtain ⟨y, hy, u', hu', rfl⟩ := c.exists_rep_of_kinds hk hx hxQS
    obtain ⟨hyX, -, hyact⟩ := c.rep_mem Kind.field y hy
    have hyπ : cj c.pi y = c.pi := (c.field_act_parts hyact).1
    have hyq : y⁻¹ * d.q * y = d.q := by
      have hqcomm := mem_centralizer_singleton_iff.1 ((d.q_mem_X h).2 hyX)
      calc y⁻¹ * d.q * y = y⁻¹ * (d.q * y) := by group
        _ = y⁻¹ * (y * d.q) := by rw [← hqcomm]
        _ = d.q := by group
    have e : (u' * y)⁻¹ * c.pi * (u' * y) = y⁻¹ * (u'⁻¹ * c.pi * u') * y := by group
    rw [e]
    rcases c.cj_pi_of_QS hα h hP hQ u' hu' with h1 | h1
    · left
      rw [h1]
      exact hyπ
    · right
      rw [h1]
      calc y⁻¹ * (d.q * c.pi) * y = (y⁻¹ * d.q * y) * (y⁻¹ * c.pi * y) := by group
        _ = d.q * c.pi := by rw [hyq]; exact congrArg _ hyπ

theorem Chart4.t_central_X (hα : α ≤ 1) (hα0 : α = 0) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hk : ∀ k', (c.rep k').isSome → k' = Kind.field) : ∀ x ∈ d.X, x * c.t = c.t * x := by
  have hcen := c.t_comm hα h hP hQ
  have hQS : ∀ x ∈ d.QS, x * c.t = c.t * x := by
    intro x hx
    obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 hx
    have h1 : c.t * u = u * c.t := d.comm_Q_S hu c.t_mem.2
    calc u * s * c.t = u * (s * c.t) := by group
      _ = u * (c.t * s) := by rw [hcen s hs]
      _ = (u * c.t) * s := by group
      _ = (c.t * u) * s := by rw [h1]
      _ = c.t * (u * s) := by group
  intro x hx
  by_cases hxQS : x ∈ d.QS
  · exact hQS x hxQS
  · obtain ⟨y, hy, u', hu', rfl⟩ := c.exists_rep_of_kinds hk hx hxQS
    obtain ⟨hyX, -, hyact⟩ := c.rep_mem Kind.field y hy
    have hyt : cj c.t y = c.t := (c.field_act_parts hyact).2.2.1 hα0
    have hyc : y * c.t = c.t * y := by
      unfold cj at hyt
      calc y * c.t = y * (y⁻¹ * c.t * y) := by rw [hyt]
        _ = c.t * y := by group
    calc u' * y * c.t = u' * (y * c.t) := by group
      _ = u' * (c.t * y) := by rw [hyc]
      _ = (u' * c.t) * y := by group
      _ = (c.t * u') * y := by rw [hQS u' hu']
      _ = c.t * (u' * y) := by group

theorem Chart4.sq_mem_Q_of_central
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hE : chExcl1OK = true)
    (hk : ∀ k', (c.rep k').isSome → k' = Kind.field) {z : G} (hz : z ∈ d.X)
    (hzπ : z * c.pi = c.pi * z)
    (hzc : ∀ x ∈ d.X, x * c.pi = c.pi * x → z * x = x * z) : z * z ∈ d.Q := by
  have hS := c.sFacts hα h hP hQ
  have hVc : ∀ v ∈ c.V, z * v = v * z := by
    intro v hv
    refine hzc v (d.S_le_X (c.V_le_S h hv)) ?_
    exact hS.V_comm v hv c.pi (subset_closure (by simp))
  rcases c.centralizing_V hα h hP hQ hS2 hz hVc with ⟨u, hu, w, hw, rfl⟩ | ⟨y, hy, -⟩
  · have hξX : c.xi ∈ d.X := d.S_le_X c.mem.2.2.2.2.2
    have hξπ : c.xi * c.pi = c.pi * c.xi := by
      have := c.frame.pi_xi
      unfold cj at this
      calc c.xi * c.pi = c.xi * (c.xi⁻¹ * c.pi * c.xi) := by rw [this]
        _ = c.pi * c.xi := by group
    have hzξ := hzc c.xi hξX hξπ
    have hwS : w ∈ d.S := hw.1
    have h1 : c.xi * u = u * c.xi := d.comm_Q_S hu c.mem.2.2.2.2.2
    have h2 : w * u = u * w := d.comm_Q_S hu hwS
    have hwξ : w * c.xi = c.xi * w := by
      have h3 : u * (w * c.xi) = u * (c.xi * w) := by
        calc u * (w * c.xi) = (u * w) * c.xi := by group
          _ = c.xi * (u * w) := hzξ
          _ = (c.xi * u) * w := by group
          _ = (u * c.xi) * w := by rw [h1]
          _ = u * (c.xi * w) := by group
      exact mul_left_cancel h3
    have hw2 := c.sq_mem_zpowers_of_comm_xi hα h hP hE hw hwξ
    have e : u * w * (u * w) = (u * u) * (w * w) := by
      calc u * w * (u * w) = u * (w * u) * w := by group
        _ = u * (u * w) * w := by rw [h2]
        _ = (u * u) * (w * w) := by group
    rw [e]
    exact d.Q.mul_mem (d.Q.mul_mem hu hu) ((zpowers_le.2 c.t_mem.1) hw2)
  · exfalso
    have hmem : Kind.graph = Kind.field := hk Kind.graph (by rw [hy]; rfl)
    cases hmem

theorem Chart4.conj_q_of_normalizer
    (hα : α ≤ 1) (hα0 : α = 0) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) (hS2 : chSec2OK = true) (hE : chExcl1OK = true)
    (hk : ∀ k', (c.rep k').isSome → k' = Kind.field) {n : G}
    (hn : n ∈ normalizer ((d.X ⊓ centralizer ({c.pi} : Set G) : Subgroup G) : Set G)) :
    n * d.q * n⁻¹ = d.q := by
  have hcen := c.t_comm hα h hP hQ
  have htX := c.t_central_X hα hα0 h hP hQ hk
  have htS : c.t ∈ d.S := c.t_mem.2
  have htπ : c.t * c.pi = c.pi * c.t := (hcen c.pi c.mem.1).symm
  have htH : c.t ∈ (d.X ⊓ centralizer ({c.pi} : Set G) : Subgroup G) :=
    ⟨d.S_le_X htS, mem_centralizer_singleton_iff.2 htπ⟩
  have ht'H := (mem_normalizer_iff.1 hn c.t).1 htH
  have hz : n * c.t * n⁻¹ ∈ d.X := ht'H.1
  have hzπ : n * c.t * n⁻¹ * c.pi = c.pi * (n * c.t * n⁻¹) :=
    mem_centralizer_singleton_iff.1 ht'H.2
  have hzc : ∀ x ∈ d.X, x * c.pi = c.pi * x → (n * c.t * n⁻¹) * x = x * (n * c.t * n⁻¹) := by
    intro x hx hxπ
    have hxH : x ∈ (d.X ⊓ centralizer ({c.pi} : Set G) : Subgroup G) :=
      ⟨hx, mem_centralizer_singleton_iff.2 hxπ⟩
    have hx' := (mem_normalizer_iff''.1 hn x).1 hxH
    have h1 := htX _ hx'.1
    calc n * c.t * n⁻¹ * x = n * (c.t * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * x * n) * c.t) * n⁻¹ := by rw [← h1]
      _ = x * (n * c.t * n⁻¹) := by group
  have hsq := c.sq_mem_Q_of_central hα h hP hQ hS2 hE hk hz hzπ hzc
  have e : n * c.t * n⁻¹ * (n * c.t * n⁻¹) = n * d.q * n⁻¹ := by
    calc n * c.t * n⁻¹ * (n * c.t * n⁻¹) = n * (c.t * c.t) * n⁻¹ := by group
      _ = n * d.q * n⁻¹ := by rw [c.q_eq, pow_two]
  rw [e] at hsq
  have hqq : d.q * d.q = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by simp [d.q_ord])
  have hord : orderOf (n * d.q * n⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, d.q_ord]
  exact d.eq_q_of_mem_centralizer h (d.Q_le_centralizer hsq) hord

end CFSG.OddStandard.ChengHeld
