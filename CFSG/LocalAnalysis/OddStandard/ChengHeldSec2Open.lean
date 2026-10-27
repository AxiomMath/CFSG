module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2UniqW

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.unitary_sq_witness (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (hS2 : chSec2OK = true) {y : G} (hy : y ∈ d.X)
    (hact : Kind.unitary.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) :
    ∃ s ∈ d.S, y⁻¹ * s * y = s ∧ (s * s = c.pi ∨ s * s = c.pi * d.q) := by
  have hS := c.sFacts hα h hP hQ
  have hmS : c.mu * c.lam * c.xi * c.tau ∈ d.S :=
    mul_mem (mul_mem (mul_mem c.mem.2.2.1 c.mem.2.2.2.1) c.mem.2.2.2.2.2) c.mem.2.1
  have hm2 : (c.mu * c.lam * c.xi * c.tau) * (c.mu * c.lam * c.xi * c.tau) = c.pi := by
    rw [← pow_two]; exact hS.sq_mlxt
  have hqS : d.q ∈ d.S := d.q_mem_S h
  have htS : c.t ∈ d.S := c.t_mem.2
  rcases c.unitary_fix_fact hα h hP hS2 hy hact with hf | hf
  · refine ⟨c.mu * c.lam * c.xi * c.tau, hmS, (hf _ hmS).2 (subset_closure (by simp)), Or.inl hm2⟩
  · have hmt : c.mu * c.lam * c.xi * c.tau * c.t ∈ d.S := mul_mem hmS htS
    refine ⟨_, hmt, (hf _ hmt).2 (subset_closure (by simp)), Or.inr ?_⟩
    have hcomm : c.t * (c.mu * c.lam * c.xi * c.tau) = (c.mu * c.lam * c.xi * c.tau) * c.t := by
      have ht : c.t ∈ d.S ⊓ centralizer (d.S : Set G) := by
        rw [hS.center]; exact mem_zpowers _
      exact (mem_centralizer_iff.1 ht.2 _ hmS).symm
    calc c.mu * c.lam * c.xi * c.tau * c.t * (c.mu * c.lam * c.xi * c.tau * c.t)
        = (c.mu * c.lam * c.xi * c.tau) * (c.t * (c.mu * c.lam * c.xi * c.tau)) * c.t := by group
      _ = (c.mu * c.lam * c.xi * c.tau) * ((c.mu * c.lam * c.xi * c.tau) * c.t) * c.t := by
          rw [hcomm]
      _ = ((c.mu * c.lam * c.xi * c.tau) * (c.mu * c.lam * c.xi * c.tau)) * (c.t * c.t) := by
          group
      _ = c.pi * d.q := by rw [hm2, c.q_eq, pow_two]

theorem Chart4.centralizing_V (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (hS2 : chSec2OK = true) {x : G}
    (hx : x ∈ d.X) (hVc : ∀ v ∈ c.V, x * v = v * x) :
    (∃ u ∈ d.Q, ∃ s ∈ c.W, x = u * s) ∨
      ∃ y, c.rep Kind.graph = some y ∧ ∃ u ∈ d.Q, ∃ s ∈ c.W, x = u * s * y := by
  by_cases hxQS : x ∈ d.QS
  · left
    obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 hxQS
    refine ⟨u, hu, s, c.mem_W_of_comm hs fun v hv => ?_, rfl⟩
    have h1 := hVc v hv
    have h2 : v * u = u * v := d.comm_Q_S hu (c.V_le_S h hv)
    have h3 : u * (s * v) = u * (v * s) := by
      calc u * (s * v) = u * s * v := by group
        _ = v * (u * s) := h1
        _ = (v * u) * s := by group
        _ = (u * v) * s := by rw [h2]
        _ = u * (v * s) := by group
    exact mul_left_cancel h3
  · exact Or.inr (c.centralizing_outside hα h hP hQ hS2 hx hxQS hVc)

end CFSG.OddStandard.ChengHeld
