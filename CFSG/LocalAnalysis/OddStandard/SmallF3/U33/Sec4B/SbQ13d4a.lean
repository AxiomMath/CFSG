module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d1c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_rho_norm_AC (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    rho ∈ normalizer (((q13A t tau x₁ x₂ rho ⊔ closure ({t, om} : Set G) : Subgroup G)) :
      Set G) := by
  have hA : rho ∈ normalizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => (q13a_A_inv h a ha).1)
  have hCO : rho ∈ normalizer ((closure ({t, om} : Set G) : Subgroup G) : Set G) := by
    have hcent : closure ({t, om} : Set G) ≤ Subgroup.centralizer ({rho} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (q13a_t_comm h).2.1
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (q13a_om_comm h).2.1
    exact Subgroup.mem_normalizer_fintype (fun c hc => by
      have hcomm : rho * c = c * rho :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hcent hc)).symm
      have hconj : rho * c * rho⁻¹ = c := by rw [hcomm]; group
      rwa [hconj])
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hA, hCO⟩

theorem q13d_rho_norm (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    rho ∈ q13L t tau x₁ x₂ rho om := by
  rw [q13L, q13d_E0_eq_AC h]
  exact q13d_rho_norm_AC h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
