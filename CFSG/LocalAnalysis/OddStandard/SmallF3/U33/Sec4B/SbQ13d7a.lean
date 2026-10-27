module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_E0_le_B (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13E0 t tau x₁ x₂ rho om ≤ q13B t tau x₁ x₂ rho om := by
  rw [q13B, q13L]
  exact le_inf Subgroup.le_normalizer (q13d_E0_le_cent_N h)

theorem q13d_B_normal (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    NormalIn (q13B t tau x₁ x₂ rho om) (q13L t tau x₁ x₂ rho om) := by
  refine ⟨inf_le_left, ?_⟩
  intro g hg k hk
  rw [q13B, Subgroup.mem_inf] at hk ⊢
  obtain ⟨hkL, hkC⟩ := hk
  refine ⟨mul_mem (mul_mem hg hkL) (inv_mem hg), ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hkC ⊢
  intro n hn
  have hgn : g⁻¹ * n * g ∈ ctxN tau x₁ x₂ := by
    simpa using q13d_N_normal_L h g⁻¹ (inv_mem hg) n hn
  have hcomm : k * (g⁻¹ * n * g) = (g⁻¹ * n * g) * k := (hkC _ hgn).symm
  exact (calc (g * k * g⁻¹) * n = g * (k * (g⁻¹ * n * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * n * g) * k) * g⁻¹ := by rw [hcomm]
    _ = n * (g * k * g⁻¹) := by group).symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
