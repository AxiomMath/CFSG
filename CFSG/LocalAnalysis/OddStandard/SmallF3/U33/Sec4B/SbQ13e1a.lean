module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_cocycle (h : Q13Om t L S x₁ x₂ lam rho tau om) {b p : G}
    (hb : (t * lam) * b * (t * lam)⁻¹ = b * p) :
    p * ((t * lam) * p * (t * lam)⁻¹) = 1 := by
  have hf : (t * lam) * (t * lam) = 1 := q13c_tlam_sq h
  have hf' : (t * lam)⁻¹ * (t * lam)⁻¹ = 1 := by
    rw [← mul_inv_rev, hf, inv_one]
  have hconj : ∀ x : G, (t * lam) * ((t * lam) * x * (t * lam)⁻¹) * (t * lam)⁻¹ = x := by
    intro x
    calc (t * lam) * ((t * lam) * x * (t * lam)⁻¹) * (t * lam)⁻¹
        = ((t * lam) * (t * lam)) * x * ((t * lam)⁻¹ * (t * lam)⁻¹) := by group
      _ = 1 * x * 1 := by rw [hf, hf']
      _ = x := by group
  have h1 : b = b * (p * ((t * lam) * p * (t * lam)⁻¹)) := by
    calc b = (t * lam) * ((t * lam) * b * (t * lam)⁻¹) * (t * lam)⁻¹ := (hconj b).symm
      _ = (t * lam) * (b * p) * (t * lam)⁻¹ := by rw [hb]
      _ = ((t * lam) * b * (t * lam)⁻¹) * ((t * lam) * p * (t * lam)⁻¹) := by group
      _ = (b * p) * ((t * lam) * p * (t * lam)⁻¹) := by rw [hb]
      _ = b * (p * ((t * lam) * p * (t * lam)⁻¹)) := by rw [mul_assoc]
  have h2 : (1 : G) = p * ((t * lam) * p * (t * lam)⁻¹) := by
    apply mul_left_cancel (a := b)
    rw [mul_one]
    exact h1
  exact h2.symm

theorem q13e_fix_rep (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om)
    {b : G} (hbL : b ∈ q13L t tau x₁ x₂ rho om)
    (hb : (t * lam) * b * (t * lam)⁻¹ * b⁻¹ ∈ q13P t tau x₁ x₂ rho om) :
    ∃ p ∈ q13P t tau x₁ x₂ rho om, (t * lam) * b * (t * lam)⁻¹ = b * p := by
  refine ⟨b⁻¹ * ((t * lam) * b * (t * lam)⁻¹ * b⁻¹) * b, ?_, ?_⟩
  · have := q13d_P_normal_L h hD.A_cent b⁻¹ (inv_mem hbL)
      ((t * lam) * b * (t * lam)⁻¹ * b⁻¹) hb
    simpa using this
  · group

theorem q13e_cocycle_change (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {b p q : G} (hb : (t * lam) * b * (t * lam)⁻¹ = b * p)
    (hp : p ∈ q13P t tau x₁ x₂ rho om) (hq : q ∈ q13P t tau x₁ x₂ rho om) :
    (t * lam) * (b * q) * (t * lam)⁻¹ = (b * q) * (p * ((t * lam) * q * (t * lam)⁻¹ * q⁻¹)) := by
  have hfL : (t * lam) ∈ q13L t tau x₁ x₂ rho om := q13e_f_mem_L h hD
  have hAP : (t * lam) * q * (t * lam)⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    q13d_P_normal_L h hD.A_cent (t * lam) hfL q hq
  have hcomm_qp : q * p = p * q := q13d_P_comm h hD.A_cent q hq p hp
  have hcomm_qA : q * ((t * lam) * q * (t * lam)⁻¹) =
      ((t * lam) * q * (t * lam)⁻¹) * q := q13d_P_comm h hD.A_cent q hq _ hAP
  have hstep : q * (p * (((t * lam) * q * (t * lam)⁻¹) * q⁻¹)) =
      p * ((t * lam) * q * (t * lam)⁻¹) := by
    calc q * (p * (((t * lam) * q * (t * lam)⁻¹) * q⁻¹))
        = q * p * ((t * lam) * q * (t * lam)⁻¹) * q⁻¹ := by group
      _ = p * q * ((t * lam) * q * (t * lam)⁻¹) * q⁻¹ := by rw [hcomm_qp]
      _ = p * (q * ((t * lam) * q * (t * lam)⁻¹)) * q⁻¹ := by group
      _ = p * (((t * lam) * q * (t * lam)⁻¹) * q) * q⁻¹ := by rw [hcomm_qA]
      _ = p * ((t * lam) * q * (t * lam)⁻¹) := by group
  calc (t * lam) * (b * q) * (t * lam)⁻¹
      = ((t * lam) * b * (t * lam)⁻¹) * ((t * lam) * q * (t * lam)⁻¹) := by group
    _ = (b * p) * ((t * lam) * q * (t * lam)⁻¹) := by rw [hb]
    _ = b * (p * ((t * lam) * q * (t * lam)⁻¹)) := by rw [mul_assoc]
    _ = b * (q * (p * (((t * lam) * q * (t * lam)⁻¹) * q⁻¹))) := by rw [hstep]
    _ = (b * q) * (p * (((t * lam) * q * (t * lam)⁻¹) * q⁻¹)) := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
