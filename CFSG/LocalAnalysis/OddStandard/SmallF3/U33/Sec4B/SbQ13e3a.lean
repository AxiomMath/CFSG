module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_conj_t (h : Q13Om t L S x₁ x₂ lam rho tau om) (g : G) : g * t * g⁻¹ = t * ⁅t, g⁆ := by
  have ht : t * t = 1 := q13a_t_mul_self h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [commutatorElement_def, hti]
  calc g * t * g⁻¹ = (t * t) * (g * t * g⁻¹) := by rw [ht, one_mul]
    _ = t * (t * (g * t * g⁻¹)) := by rw [mul_assoc]
    _ = t * (t * g * t * g⁻¹) := by group

theorem q13e_t_conj (h : Q13Om t L S x₁ x₂ lam rho tau om) (g : G) : t * g * t = ⁅t, g⁆ * g := by
  have ht : t * t = 1 := q13a_t_mul_self h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [commutatorElement_def, hti]
  group

theorem q13e_kap_mem_P (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, ⁅t, g⁆ ∈ q13P t tau x₁ x₂ rho om := by
  intro g hg
  obtain ⟨p, hp, hp_eq⟩ := Set.mem_smul_set.mp (hD.tL g hg)
  rw [smul_eq_mul, q13e_conj_t h g] at hp_eq
  have hpe : p = ⁅t, g⁆ := mul_left_cancel hp_eq
  rw [← hpe]
  exact hp

theorem q13e_kap_P (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, ⁅t, p⁆ = (p ^ 2)⁻¹ := by
  intro p hp
  rw [commutatorElement_def, hD.t_inv_P p hp, pow_two, mul_inv_rev]

theorem q13e_kap_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ e ∈ q13E0 t tau x₁ x₂ rho om, ⁅t, e⁆ ∈ ctxN tau x₁ x₂ := by
  intro e he
  rw [q13d_mem_E0 h hD.A_cent] at he
  rcases he with he | ⟨p, hp, hep⟩
  · rw [q13e_kap_P h hD e he]
    exact inv_mem (q13d_P_sq_mem_N h hD.A_cent e he)
  · rw [hep]
    have hEq : ⁅t, t * p⁆ = p ^ 2 := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      simp only [commutatorElement_self, one_mul]
      rw [q13e_kap_P h hD p hp, hD.t_inv_P (p ^ 2)⁻¹ (inv_mem (pow_mem hp 2)), inv_inv]
    rw [hEq]
    exact q13d_P_sq_mem_N h hD.A_cent p hp

theorem q13e_kap_onto_N (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ n ∈ ctxN tau x₁ x₂, ∃ p ∈ q13P t tau x₁ x₂ rho om, ⁅t, p⁆ = n := by
  intro n hn
  obtain ⟨p, hp, hp_eq⟩ := q13e_exists_sq h hD n hn
  refine ⟨p⁻¹, inv_mem hp, ?_⟩
  rw [q13e_kap_P h hD p⁻¹ (inv_mem hp), inv_pow, inv_inv, hp_eq]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
