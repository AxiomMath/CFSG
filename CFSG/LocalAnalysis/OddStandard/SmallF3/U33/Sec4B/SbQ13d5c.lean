module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d3b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_P_normal_L (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, ∀ p ∈ q13P t tau x₁ x₂ rho om, g * p * g⁻¹
      ∈ q13P t tau x₁ x₂ rho om := by
  intro g hg p hp
  exact q13d_conj_mem_of_charIn (q13d_P_char_E0 h hII) hg p hp

theorem q13d_tL (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, g * t * g⁻¹ ∈ t • (q13P t tau x₁ x₂ rho om : Set G) := by
  intro g hg
  have hgE : g * t * g⁻¹ ∈ q13E0 t tau x₁ x₂ rho om :=
    (Subgroup.mem_normalizer_iff.mp hg t).mp (q13d_t_mem_E0 h)
  rcases (q13d_mem_E0 h hII).mp hgE with hP | ⟨p, hp, hpx⟩
  · exfalso
    apply q13d_t_not_mem_P h hII
    have hconj := q13d_P_normal_L h hII g⁻¹ (inv_mem hg) (g * t * g⁻¹) hP
    simp only [inv_inv] at hconj
    rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at hconj
  · rw [Set.mem_smul_set]
    exact ⟨p, hp, by rw [smul_eq_mul]; exact hpx.symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
