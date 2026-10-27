module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

section Omega

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) {ω : G} (hω : ω = tau ∨ ω = t * tau)
include hc hω

theorem omega_mul_self : ω * ω = 1 := by
  rcases hω with rfl | rfl
  · exact hc.tau_mul_self
  · calc (t * tau) * (t * tau) = t * (tau * t) * tau := by group
      _ = t * (t * tau) * tau := by rw [← hc.t_comm_tau]
      _ = (t * t) * (tau * tau) := by group
      _ = 1 := by rw [hc.t_mul_self, hc.tau_mul_self, one_mul]

theorem omega_not_mem_V : ω ∉ fourGrp x₁ x₂ := by
  rcases hω with rfl | rfl
  · exact fun h => hc.tau_not_mem_Q (hc.V_le_Q h)
  · exact fun h => hc.ttau_not_mem_Q (hc.V_le_Q h)

theorem omega_comm_V : ∀ a ∈ fourGrp x₁ x₂, ω * a = a * ω := by
  intro a ha
  have hXω : ω ∈ closure ({t, tau} : Set G) := by
    rcases hω with rfl | rfl
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hXa : a ∈ closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} : Set G) := by
    rw [fourGrp] at ha
    exact Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto) ha
  exact (Ctx4.centralizer_t_tau hc.toCtx4).2.2.2.2 ω hXω a hXa

theorem q_comm_omega : (t * lam) * ω = ω * (t * lam) := by
  rcases hω with rfl | rfl
  · exact q_comm_tau hc
  · exact q_comm_ttau hc

theorem mem_ctxN_iff (u : G) : u ∈ ctxN ω x₁ x₂ ↔
    u ∈ fourGrp x₁ x₂ ∨ ∃ a ∈ fourGrp x₁ x₂, u = ω * a := by
  constructor
  · intro hu
    rw [ctxN] at hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inr ⟨1, one_mem _, by rw [mul_one]⟩
      · exact Or.inl (subset_closure (by simp))
      · exact Or.inl (subset_closure (by simp))
    | one => exact Or.inl (one_mem _)
    | mul x y _ _ ihx ihy =>
      rcases ihx with hxV | ⟨b, hbV, rfl⟩ <;> rcases ihy with hyV | ⟨c, hcV, rfl⟩
      · exact Or.inl (mul_mem hxV hyV)
      · refine Or.inr ⟨x * c, mul_mem hxV hcV, ?_⟩
        rw [← mul_assoc, (omega_comm_V hc hω x hxV).symm, mul_assoc]
      · refine Or.inr ⟨b * y, mul_mem hbV hyV, ?_⟩
        rw [mul_assoc]
      · refine Or.inl ?_
        have hbc : (ω * b) * (ω * c) = b * c := by
          have hb' : ω * b = b * ω := omega_comm_V hc hω b hbV
          calc (ω * b) * (ω * c) = (b * ω) * (ω * c) := by rw [hb']
            _ = b * (ω * (ω * c)) := by group
            _ = b * ((ω * ω) * c) := by group
            _ = b * c := by rw [omega_mul_self hc hω, one_mul]
        rw [hbc]; exact mul_mem hbV hcV
    | inv x _ ihx =>
      rcases ihx with hxV | ⟨b, hbV, rfl⟩
      · exact Or.inl (inv_mem hxV)
      · refine Or.inr ⟨b⁻¹, inv_mem hbV, ?_⟩
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (omega_mul_self hc hω),
          (omega_comm_V hc hω b⁻¹ (inv_mem hbV)).symm]
  · rintro (hu | ⟨a, ha, rfl⟩)
    · rw [ctxN]
      exact Subgroup.closure_mono (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        tauto) hu
    · rw [ctxN]
      exact mul_mem (subset_closure (by simp)) (Subgroup.closure_mono (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        tauto) ha)

end Omega

end CFSG.OddStandard.SmallF3.HarrisU33.L34
