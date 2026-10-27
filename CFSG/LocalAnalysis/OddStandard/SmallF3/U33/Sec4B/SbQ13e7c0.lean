module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13e_y_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ ^ 2 * x₁ ^ 2 = 1 := by
  have h4 : x₁ ^ 4 = 1 := by
    have := pow_orderOf_eq_one x₁
    rwa [(q13a_x₁_facts h).2.2.1] at this
  rw [← pow_add, show (2 : ℕ) + 2 = 4 from rfl, h4]

private lemma q13e_u_sq_aux (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {x : G} (hxL : x ∈ q13L t tau x₁ x₂ rho om)
    (hxtau : x * tau * x⁻¹ = x ^ 2 * tau) (hx2V : x ^ 2 ∈ fourGrp x₁ x₂) :
    ((t * om)⁻¹ * (x * (t * om) * x⁻¹)) ^ 2 = x ^ 2 := by
  set γ := t * om with hγ
  have hγP : γ ∈ q13P t tau x₁ x₂ rho om := q13d_gam_mem_P h
  have hwP : x * γ * x⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    q13d_P_normal_L h hD.A_cent x hxL γ hγP
  have hcomm : Commute γ (x * γ * x⁻¹) :=
    q13d_P_comm h hD.A_cent γ hγP (x * γ * x⁻¹) hwP
  have hsq : (γ⁻¹ * (x * γ * x⁻¹)) ^ 2 = (γ⁻¹) ^ 2 * (x * γ * x⁻¹) ^ 2 :=
    hcomm.inv_left.mul_pow 2
  have hγinv : (γ⁻¹) ^ 2 = tau := by
    rw [inv_pow, hγ, hD.gam_sq]
    exact inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)
  have hw : (x * γ * x⁻¹) ^ 2 = x * tau * x⁻¹ := by
    rw [pow_two, show (x * γ * x⁻¹) * (x * γ * x⁻¹) = x * (γ * γ) * x⁻¹ by group,
      ← pow_two, hγ, hD.gam_sq]
  have hx2A : x ^ 2 ∈ q13A t tau x₁ x₂ rho := q13a_V_le_A h hx2V
  have htau_comm : tau * x ^ 2 = x ^ 2 * tau := (q13d_A_cent_tau h (x ^ 2) hx2A).symm
  calc (γ⁻¹ * (x * γ * x⁻¹)) ^ 2
      = (γ⁻¹) ^ 2 * (x * γ * x⁻¹) ^ 2 := hsq
    _ = tau * (x * tau * x⁻¹) := by rw [hγinv, hw]
    _ = tau * (x ^ 2 * tau) := by rw [hxtau]
    _ = x ^ 2 := by rw [← mul_assoc, htau_comm, mul_assoc, q13a_tau_mul_self h, mul_one]

theorem q13e_u_mem_P (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ x ∈ q13L t tau x₁ x₂ rho om, (t * om)⁻¹ * (x * (t * om) * x⁻¹) ∈ q13P t tau x₁ x₂ rho om := by
  intro x hx
  exact (q13P t tau x₁ x₂ rho om).mul_mem
    ((q13P t tau x₁ x₂ rho om).inv_mem (q13d_gam_mem_P h))
    (q13d_P_normal_L h hD.A_cent x hx (t * om) (q13d_gam_mem_P h))

theorem q13e_u_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ((t * om)⁻¹ * (x₁ * (t * om) * x₁⁻¹)) ^ 2 = x₁ ^ 2 ∧
      ((t * om)⁻¹ * (x₂ * (t * om) * x₂⁻¹)) ^ 2 = x₂ ^ 2 := by
  obtain ⟨hx₁L, hx₂L⟩ := q13e_x_mem_L h hD
  obtain ⟨htau₁, htau₂⟩ := q13e_x_tau h
  obtain ⟨hx₁V, hx₂V⟩ := q13e_x_sq_mem_V h
  exact ⟨q13e_u_sq_aux h hD hx₁L htau₁ hx₁V, q13e_u_sq_aux h hD hx₂L htau₂ hx₂V⟩

theorem q13e_AN_cover (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om)
    {u₁ u₂ : G} (hu₁ : u₁ ∈ q13P t tau x₁ x₂ rho om) (hu₂ : u₂ ∈ q13P t tau x₁ x₂ rho om)
    (h₁ : u₁ ^ 2 = x₁ ^ 2) (h₂ : u₂ ^ 2 = x₂ ^ 2) :
    ∀ a ∈ q13AN t tau x₁ x₂ rho,
      a ∈ ctxN tau x₁ x₂ ∨ a * u₁⁻¹ ∈ ctxN tau x₁ x₂ ∨ a * u₂⁻¹ ∈ ctxN tau x₁ x₂ ∨
      a * (u₁ * u₂)⁻¹ ∈ ctxN tau x₁ x₂ := by
  intro a ha
  obtain ⟨haP, ha2V⟩ := (q13e_mem_AN h hD).mp ha
  have hcomm₁ : Commute a u₁ := q13d_P_comm h hD.A_cent a haP u₁ hu₁
  have hcomm₂ : Commute a u₂ := q13d_P_comm h hD.A_cent a haP u₂ hu₂
  have hcomm₁₂ : Commute u₁ u₂ := q13d_P_comm h hD.A_cent u₁ hu₁ u₂ hu₂
  rcases (q13e_mem_V h).mp ha2V with h0 | h1 | hz | hyz
  · exact Or.inl (q13d_P_sq_eq_one_mem_N h hD.A_cent a haP h0)
  · refine Or.inr (Or.inl ?_)
    have hdP : a * u₁⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
      (q13P t tau x₁ x₂ rho om).mul_mem haP ((q13P t tau x₁ x₂ rho om).inv_mem hu₁)
    exact q13d_P_sq_eq_one_mem_N h hD.A_cent _ hdP (by
      rw [(hcomm₁.inv_right).mul_pow 2, inv_pow, h₁, h1, mul_inv_cancel])
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hprod2 : (u₁ * u₂) ^ 2 = (x₁ * x₂) ^ 2 := by
      rw [hcomm₁₂.mul_pow 2, h₁, h₂, q13e_x₂_sq h, ← mul_assoc, q13e_y_sq h, one_mul]
    have hdP : a * (u₁ * u₂)⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
      (q13P t tau x₁ x₂ rho om).mul_mem haP
        ((q13P t tau x₁ x₂ rho om).inv_mem ((q13P t tau x₁ x₂ rho om).mul_mem hu₁ hu₂))
    exact q13d_P_sq_eq_one_mem_N h hD.A_cent _ hdP (by
      rw [(hcomm₁.mul_right hcomm₂).inv_right.mul_pow 2, inv_pow, hprod2, hz, mul_inv_cancel])
  · refine Or.inr (Or.inr (Or.inl ?_))
    have hdP : a * u₂⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
      (q13P t tau x₁ x₂ rho om).mul_mem haP ((q13P t tau x₁ x₂ rho om).inv_mem hu₂)
    exact q13d_P_sq_eq_one_mem_N h hD.A_cent _ hdP (by
      rw [(hcomm₂.inv_right).mul_pow 2, inv_pow, h₂, hyz, ← q13e_x₂_sq h, mul_inv_cancel])

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
