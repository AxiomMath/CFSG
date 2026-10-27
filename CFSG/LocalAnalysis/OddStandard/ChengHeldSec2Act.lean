module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Model

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.sq_mem_Q (hα : α ≤ 1)
    (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true) (k : Kind)
    {y : G} (hy : y ∈ d.X) (hact : k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) :
    y * y ∈ d.Q := by
  have hA := c.autFactsG hα h hP hQ k hy hact
  have hc : y * y ∈ centralizer (d.S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    have := hA.invol s hs
    have h1 : y⁻¹ * (y⁻¹ * s * y) * y = y⁻¹ * y⁻¹ * s * (y * y) := by group
    rw [h1] at this
    calc s * (y * y) = y * y * (y⁻¹ * y⁻¹ * s * (y * y)) := by group
      _ = y * y * s := by rw [this]
  exact c.centralizer_X_S_le_Q hα h hP hQ ⟨d.X.mul_mem hy hy, hc⟩

theorem Datum.conj_mem_QS (d : Datum A) {x u : G} (hx : x ∈ d.X) (hu : u ∈ d.QS) :
    x * u * x⁻¹ ∈ d.QS := by
  obtain ⟨a, ha, b, hb, rfl⟩ := d.mem_QS_iff.1 hu
  have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
  rw [this]
  exact d.mem_QS_iff.2 ⟨_, d.conj_mem_Q hx ha, _, d.conj_mem_S hx hb, rfl⟩

theorem Chart4.sq_mem_QS
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    {x : G} (hx : x ∈ d.X) : x * x ∈ d.QS := by
  by_cases hxQS : x ∈ d.QS
  · exact mul_mem hxQS hxQS
  · obtain ⟨k, y₀, hrep, u, hu, rfl⟩ := c.cover x hx hxQS
    obtain ⟨hy₀, -, hact⟩ := c.rep_mem k y₀ hrep
    have e : u * y₀ * (u * y₀) = u * (y₀ * u * y₀⁻¹) * (y₀ * y₀) := by group
    rw [e]
    exact mul_mem (mul_mem hu (d.conj_mem_QS hy₀ hu))
      (mem_sup_left (c.sq_mem_Q hα h hP hQ k hy₀ hact))

theorem Chart4.act_of_involution
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) (k : Kind)
    {y : G} (hy : y ∈ d.X) (hact : k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) {z : G}
    (hz2 : z * z = 1) (hzy : ∃ u ∈ d.QS, z = u * y) :
    ∃ s ∈ d.S, ∃ x ∈ d.Q, cj z s = y * x := by
  obtain ⟨u₀, hu₀, rfl⟩ := hzy
  obtain ⟨u, hu, s₀, hs₀, rfl⟩ := d.mem_QS_iff.1 hu₀
  have hQS : ∀ q ∈ d.Q, ∀ s ∈ d.S, s * q = q * s := fun q hq s hs =>
    mem_centralizer_iff.1 (d.Q_le_centralizer_S hq) s hs
  have hyy : y * y ∈ d.Q := c.sq_mem_Q hα h hP hQ k hy hact
  have hũ : y * u * y⁻¹ ∈ d.Q := d.conj_mem_Q hy hu
  have hσS : y⁻¹ * s₀ * y ∈ d.S := d.conj_inv_mem_S hy s₀ hs₀
  have key : u * s₀ * y * (u * s₀ * y) =
      (u * (y * u * y⁻¹) * (y * y)) * (s₀ * (y⁻¹ * s₀ * y)) := by
    have h1 : s₀ * (y * u * y⁻¹) = (y * u * y⁻¹) * s₀ := hQS _ hũ s₀ hs₀
    have h2 : s₀ * (y * y) = (y * y) * s₀ := hQS _ hyy s₀ hs₀
    calc u * s₀ * y * (u * s₀ * y)
        = u * (s₀ * (y * u * y⁻¹)) * ((y * y) * (y⁻¹ * s₀ * y)) := by group
      _ = u * ((y * u * y⁻¹) * s₀) * ((y * y) * (y⁻¹ * s₀ * y)) := by rw [h1]
      _ = u * (y * u * y⁻¹) * (s₀ * (y * y)) * (y⁻¹ * s₀ * y) := by group
      _ = u * (y * u * y⁻¹) * ((y * y) * s₀) * (y⁻¹ * s₀ * y) := by rw [h2]
      _ = _ := by group
  rw [key] at hz2
  have hQ' : u * (y * u * y⁻¹) * (y * y) ∈ d.Q := mul_mem (mul_mem hu hũ) hyy
  have hinv : s₀ * (y⁻¹ * s₀ * y) = (u * (y * u * y⁻¹) * (y * y))⁻¹ :=
    eq_inv_of_mul_eq_one_right hz2
  have hzt : s₀ * (y⁻¹ * s₀ * y) ∈ zpowers c.t := by
    rw [← c.Q_inf_S_eq hc]
    exact ⟨by rw [hinv]; exact d.Q.inv_mem hQ', mul_mem hs₀ hσS⟩
  obtain ⟨s, hs, hm⟩ := c.twist_fact hα h hP hS2 k hy hact hs₀ hzt
  have hmQ : s⁻¹ * s₀ * (y⁻¹ * s * y) ∈ d.Q :=
    (zpowers_le.2 c.t_mem.1) hm
  refine ⟨s, hs, y⁻¹ * (u * (s⁻¹ * s₀ * (y⁻¹ * s * y))) * y, ?_, ?_⟩
  · have := d.conj_mem_Q (d.X.inv_mem hy) (mul_mem hu hmQ)
    simpa using this
  · have h3 : s⁻¹ * u = u * s⁻¹ := by
      have := hQS u hu s⁻¹ (inv_mem hs)
      exact this
    have h4 : y * s * y⁻¹ = y⁻¹ * s * y := by
      have h2 : s * (y * y) = (y * y) * s := hQS _ hyy s hs
      calc y * s * y⁻¹ = y⁻¹ * ((y * y) * s) * y⁻¹ := by group
        _ = y⁻¹ * (s * (y * y)) * y⁻¹ := by rw [h2]
        _ = y⁻¹ * s * y := by group
    unfold cj
    calc s⁻¹ * (u * s₀ * y) * s
        = (s⁻¹ * u) * s₀ * (y * s * y⁻¹) * y := by group
      _ = u * (s⁻¹ * s₀ * (y⁻¹ * s * y)) * y := by rw [h3, h4]; group
      _ = y * (y⁻¹ * (u * (s⁻¹ * s₀ * (y⁻¹ * s * y))) * y) := by group

theorem Chart4.act_of_involution_rep
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {k : Kind}
    {y : G} (hy : c.rep k = some y) {z : G} (hz2 : z * z = 1)
    (hzy : ∃ u ∈ d.QS, z = u * y) : ∃ s ∈ d.S, ∃ x ∈ d.Q, cj z s = y * x := by
  obtain ⟨hyX, -, hact⟩ := c.rep_mem k y hy
  exact c.act_of_involution hα h hP hQ hS2 hc k hyX hact hz2 hzy

end CFSG.OddStandard.ChengHeld
