module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13d_mem_zpowers_t (h : Q13Om t L S x₁ x₂ lam rho tau om) {k : G}
    (hk : k ∈ zpowers t) : k = 1 ∨ k = t := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  rw [zpow_eq_zpow_emod' m (show t ^ 2 = 1 by rw [pow_two]; exact q13a_t_mul_self h)]
  rcases Int.emod_two_eq_zero_or_one m with hm | hm
  · left
    have hm' : m % ((2 : ℕ) : ℤ) = 0 := by simpa using hm
    rw [hm', zpow_zero]
  · right
    have hm' : m % ((2 : ℕ) : ℤ) = 1 := by simpa using hm
    rw [hm', zpow_one]

theorem q13d_mem_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) {x : G} :
    x ∈ q13E0 t tau x₁ x₂ rho om ↔ x ∈ q13P t tau x₁ x₂ rho om ∨ ∃ p ∈ q13P t tau x₁ x₂ rho om,
      x = t * p := by
  have hnorm : ∀ k ∈ zpowers t, ∀ p ∈ q13P t tau x₁ x₂ rho om,
      k * p * k⁻¹ ∈ q13P t tau x₁ x₂ rho om := by
    intro k hk p hp
    rcases q13d_mem_zpowers_t h hk with hk1 | hkt
    · rw [hk1]; simpa using hp
    · rw [hkt, q13d_t_inv_P h hII p hp]
      exact Subgroup.inv_mem _ hp
  rw [q13E0]
  constructor
  · intro hx
    obtain ⟨p, hp, k, hk, rfl⟩ :=
      (mem_sup_iff_of_normalizes (H := q13P t tau x₁ x₂ rho om) (K := zpowers t) hnorm).mp hx
    rcases q13d_mem_zpowers_t h hk with hk1 | hkt
    · left; rw [hk1, mul_one]; exact hp
    · right
      refine ⟨p⁻¹, Subgroup.inv_mem _ hp, ?_⟩
      rw [hkt]
      have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right (q13a_t_mul_self h)
      have hconj : t * p * t = p⁻¹ := by
        simpa only [ht] using q13d_t_inv_P h hII p hp
      calc p * t = (t * t) * p * t := by rw [q13a_t_mul_self h, one_mul]
        _ = t * (t * p * t) := by group
        _ = t * p⁻¹ := by rw [hconj]
  · rintro (hx | ⟨p, hp, rfl⟩)
    · exact Subgroup.mem_sup_left hx
    · exact (q13P t tau x₁ x₂ rho om ⊔ zpowers t).mul_mem
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_left hp)

theorem q13d_E0_out_sq (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, (t * p) * (t * p) = 1 := by
  intro p hp
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right (q13a_t_mul_self h)
  calc (t * p) * (t * p) = (t * p * t⁻¹) * p := by rw [ht]; group
    _ = p⁻¹ * p := by rw [q13d_t_inv_P h hII p hp]
    _ = 1 := inv_mul_cancel p

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
