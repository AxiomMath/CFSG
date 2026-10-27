module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e7c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_R_sq_mem_AN (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ r ∈ q13R t tau x₁ x₂ rho om, r * r ∈ q13AN t tau x₁ x₂ rho := by
  intro r hr
  have ht : t * t = 1 := q13a_t_mul_self h
  have hrB : r ∈ q13B t tau x₁ x₂ rho om := q13e_R_le_B hr
  have hc₀AN : ⁅t, r⁆ ∈ q13AN t tau x₁ x₂ rho := q13e_kap_mem_AN h hB hC hD r hrB
  have hc₀sqV : ⁅t, r⁆ ^ 2 ∈ fourGrp x₁ x₂ := ((q13e_mem_AN h hD).mp hc₀AN).2
  have hrrP : r * r ∈ q13P t tau x₁ x₂ rho om := q13e_B_sq_mem_P h hB hC hD r hrB
  have hcomm : r * ⁅t, r⁆ = ⁅t, r⁆ * r := q13e_R_cent_AN h hB hC hD r hr ⁅t, r⁆ hc₀AN
  have h1 : t * (r * r) * t = ⁅t, r⁆ ^ 2 * (r * r) := by
    calc t * (r * r) * t = t * r * r * t := by group
      _ = t * r * (t * t) * r * t := by rw [ht]; group
      _ = (t * r * t) * (t * r * t) := by group
      _ = (⁅t, r⁆ * r) * (⁅t, r⁆ * r) := by rw [q13e_t_conj h r]
      _ = ⁅t, r⁆ ^ 2 * (r * r) := by
        calc (⁅t, r⁆ * r) * (⁅t, r⁆ * r)
            = ⁅t, r⁆ * (r * ⁅t, r⁆) * r := by group
          _ = ⁅t, r⁆ * (⁅t, r⁆ * r) * r := by rw [hcomm]
          _ = ⁅t, r⁆ ^ 2 * (r * r) := by rw [pow_two]; group
  have h2 : t * (r * r) * t = (r * r)⁻¹ := by
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have h := hD.t_inv_P (r * r) hrrP
    rwa [hti] at h
  have h3 : (r * r)⁻¹ = ⁅t, r⁆ ^ 2 * (r * r) := by rw [← h2, h1]
  have h4 : (r * r) * (r * r) = (⁅t, r⁆ ^ 2)⁻¹ := by
    have hmul : ⁅t, r⁆ ^ 2 * ((r * r) * (r * r)) = 1 := by
      calc ⁅t, r⁆ ^ 2 * ((r * r) * (r * r))
          = (⁅t, r⁆ ^ 2 * (r * r)) * (r * r) := by group
        _ = (r * r)⁻¹ * (r * r) := by rw [← h3]
        _ = 1 := by group
    exact eq_inv_of_mul_eq_one_right hmul
  have hsqV : (r * r) ^ 2 ∈ fourGrp x₁ x₂ := by
    rw [pow_two, h4]
    exact (fourGrp x₁ x₂).inv_mem hc₀sqV
  exact (q13e_mem_AN h hD).mpr ⟨hrrP, hsqV⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
