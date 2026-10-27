module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem mem_zpowers_tau {c : G} (hc : c ∈ zpowers tau) : c = 1 ∨ c = tau := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h2 : tau ^ (2 : ℕ) = 1 := by rw [pow_two, hg.tau_mul_self]
  have hmod : tau ^ n = tau ^ (n % 2) := zpow_eq_zpow_emod' n h2
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [hmod, h]; simp
  · right; rw [hmod, h]; simp

theorem center_Qtau (htau : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹) :
    (ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) ⊓
        centralizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers tau : Subgroup G) : Set G) =
      ctxYq t tau x₁ x₂ rho := by
  have hτP : tau ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := mem_sup_right (mem_zpowers tau)
  have hzM : zpowers tau ≤ ctxM t tau x₁ x₂ := Subgroup.zpowers_le.mpr hg.tau_mem_M
  apply le_antisymm
  · rintro z ⟨hzP, hzC⟩
    obtain ⟨q, hq, c, hc, rfl⟩ := mem_sup_of_normalizes
      (fun c hc a ha => hg.normal_Q.2 c (hzM hc) a ha) hzP
    have hQP : ∀ a ∈ ctxQ t tau x₁ x₂ rho, a ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau :=
      fun a ha => mem_sup_left ha
    rcases hg.mem_zpowers_tau hc with h | h
    · rw [h, mul_one] at hzC ⊢
      have h1 : tau * q = q * tau := mem_centralizer_iff.mp hzC tau hτP
      have h2 := htau q hq
      have h3 : q ^ 2 = 1 := by
        have h4 : tau * q * tau⁻¹ = q := by rw [h1]; group
        rw [h4] at h2
        calc q ^ 2 = q * q := pow_two q
          _ = q * q⁻¹⁻¹ := by rw [inv_inv]
          _ = 1 := by rw [← h2]; group
      exact (hg.mem_Y_iff q).mpr ⟨hq, h3⟩
    · exfalso
      rw [h] at hzC
      have hall : ∀ a ∈ ctxQ t tau x₁ x₂ rho, a ^ 2 = 1 := by
        intro a ha
        have h1 : a * (q * tau) = (q * tau) * a := mem_centralizer_iff.mp hzC a (hQP a ha)
        have h2 : q * (a * tau) = q * (tau * a) := by
          calc q * (a * tau) = (q * a) * tau := by rw [mul_assoc]
            _ = (a * q) * tau := by rw [hg.Q_comm q hq a ha]
            _ = a * (q * tau) := by rw [mul_assoc]
            _ = (q * tau) * a := h1
            _ = q * (tau * a) := by rw [mul_assoc]
        have h3 : a * tau = tau * a := mul_left_cancel h2
        have h4 : tau * a * tau⁻¹ = a := by rw [← h3]; group
        have h5 := htau a ha
        rw [h4] at h5
        calc a ^ 2 = a * a := pow_two a
          _ = a * a⁻¹⁻¹ := by rw [inv_inv]
          _ = 1 := by rw [← h5]; group
      exact hg.y_ne_one (hall x₁ hg.x₁_mem_Q)
  · intro a ha
    have haQ : a ∈ ctxQ t tau x₁ x₂ rho := hg.Y_le_Q ha
    refine ⟨mem_sup_left haQ, mem_centralizer_iff.mpr fun h hh => ?_⟩
    have hP : ctxQ t tau x₁ x₂ rho ⊔ zpowers tau ≤ centralizer ({a} : Set G) := by
      refine sup_le (fun q hq => ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact mem_centralizer_singleton_iff.mpr (hg.Q_comm q hq a haQ)
      · exact mem_centralizer_singleton_iff.mpr (hg.tau_cent a ha)
    exact mem_centralizer_singleton_iff.mp (hP hh)

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
