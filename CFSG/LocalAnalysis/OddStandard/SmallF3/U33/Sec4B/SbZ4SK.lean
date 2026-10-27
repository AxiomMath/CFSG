module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem not_cent_t_Y : ¬ ∀ a ∈ ctxYq t tau x₁ x₂ rho, t * a = a * t := by
  intro h
  have hle : ctxYq t tau x₁ x₂ rho ≤ fourGrp x₁ x₂ := by
    intro a ha
    rw [← hp.CY_t]
    exact ⟨ha, mem_centralizer_iff.mpr fun g hg => by
      rw [Set.mem_singleton_iff.mp hg]; exact h a ha⟩
  have h2 := Subgroup.card_le_of_le hle
  rw [hp.card_Y, hp.card_V] at h2
  omega

end Z4Pre

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem cent_M_Y :
    ctxM t tau x₁ x₂ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
  apply le_antisymm
  · rintro k ⟨hkM, hkC⟩
    have hkY : ∀ a ∈ ctxYq t tau x₁ x₂ rho, a * k = k * a := fun a ha =>
      mem_centralizer_iff.mp hkC a ha
    have hkO : k ∈ ctxO t tau x₁ x₂ := by
      rw [hg.O_eq_CV]
      exact ⟨hkM, mem_centralizer_iff.mpr fun v hv => hkY v (hg.V_le_Y hv)⟩
    rw [hg.O_eq_Q] at hkO
    have hcl : closure ({t, tau} : Set G) ≤ ctxM t tau x₁ x₂ := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact hg.t_mem_M
      · exact hg.tau_mem_M
    obtain ⟨q, hq, c, hc, rfl⟩ := mem_sup_of_normalizes
      (fun c hc a ha => hg.normal_Q.2 c (hcl hc) a ha) hkO
    have hqY : ∀ a ∈ ctxYq t tau x₁ x₂ rho, a * q = q * a := fun a ha =>
      hg.Q_comm a (hg.Y_le_Q ha) q hq
    rcases (S4B.mem_closure_pair_of_invol hg.t_mul_self hg.tau_mul_self hg.t_comm_tau).mp hc with
      h | h | h | h
    · rw [h, mul_one]
      exact mem_sup_left hq
    · exfalso
      apply hg.not_cent_t_Y
      intro a ha
      have h1 := hkY a ha
      rw [h] at h1
      have h2 : q * (a * t) = q * (t * a) := by
        calc q * (a * t) = (q * a) * t := by rw [mul_assoc]
          _ = (a * q) * t := by rw [hqY a ha]
          _ = a * (q * t) := by rw [mul_assoc]
          _ = (q * t) * a := h1
          _ = q * (t * a) := by rw [mul_assoc]
      exact (mul_left_cancel h2).symm
    · rw [h]
      exact mul_mem (mem_sup_left hq) (mem_sup_right (mem_zpowers tau))
    · exfalso
      apply hg.not_cent_t_Y
      intro a ha
      have h1 := hkY a ha
      rw [h] at h1
      have h3 := hg.tau_cent a ha
      have h2 : q * (a * (t * tau)) = q * ((t * tau) * a) := by
        calc q * (a * (t * tau)) = (q * a) * (t * tau) := by rw [mul_assoc]
          _ = (a * q) * (t * tau) := by rw [hqY a ha]
          _ = a * (q * (t * tau)) := by rw [mul_assoc]
          _ = (q * (t * tau)) * a := h1
          _ = q * ((t * tau) * a) := by rw [mul_assoc]
      have h4 := mul_left_cancel h2
      have h5 : a * t * tau = t * a * tau := by
        calc a * t * tau = a * (t * tau) := by rw [mul_assoc]
          _ = (t * tau) * a := h4
          _ = t * (tau * a) := by rw [mul_assoc]
          _ = t * (a * tau) := by rw [h3]
          _ = t * a * tau := by rw [mul_assoc]
      exact (mul_right_cancel h5).symm
  · refine sup_le (fun q hq => ⟨hg.Q_le_M hq, ?_⟩) (Subgroup.zpowers_le.mpr ⟨hg.tau_mem_M, ?_⟩)
    · exact mem_centralizer_iff.mpr fun a ha => hg.Q_comm a (hg.Y_le_Q ha) q hq
    · exact mem_centralizer_iff.mpr fun a ha => (hg.tau_cent a ha).symm

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
