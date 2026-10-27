module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_BU_two (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    IsPGroup 2 (q13B t tau x₁ x₂ rho om ⊔ ctxU t tau x₁ x₂ lam : Subgroup G) := by
  refine IsPGroup.to_sup_of_normal_left' hD.B_two (q13b_isPGroup_U h) ?_
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact hD.B_normal.2 u (hD.M_le_L (q13b_U_le_M h hu)) b hb
  · intro hb
    have hu' : u⁻¹ ∈ ctxU t tau x₁ x₂ lam := (ctxU t tau x₁ x₂ lam).inv_mem hu
    have hmem : u⁻¹ * (u * b * u⁻¹) * u ∈ q13B t tau x₁ x₂ rho om := by
      simpa only [inv_inv] using
        hD.B_normal.2 u⁻¹ (hD.M_le_L (q13b_U_le_M h hu')) (u * b * u⁻¹) hb
    rwa [show u⁻¹ * (u * b * u⁻¹) * u = b by group] at hmem

theorem q13e_CB_f (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om,
      (t * lam) * b = b * (t * lam) → b ∈ q13E0 t tau x₁ x₂ rho om := by
  intro b hb hcomm
  have hS : IsPGroup 2 (q13B t tau x₁ x₂ rho om ⊔ ctxU t tau x₁ x₂ lam : Subgroup G) :=
    q13e_BU_two h hD
  have hU : ctxU t tau x₁ x₂ lam ≤
      (q13B t tau x₁ x₂ rho om ⊔ ctxU t tau x₁ x₂ lam : Subgroup G) := le_sup_right
  have hbS : b ∈ (q13B t tau x₁ x₂ rho om ⊔ ctxU t tau x₁ x₂ lam : Subgroup G) :=
    Subgroup.mem_sup_left hb
  have hbcent : b ∈ centralizer ({t * lam} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hbCS : b ∈ (q13B t tau x₁ x₂ rho om ⊔ ctxU t tau x₁ x₂ lam : Subgroup G) ⊓
      centralizer ({t * lam} : Set G) := ⟨hbS, hbcent⟩
  rw [hC.C_eq _ hS hU] at hbCS
  have hbU : b ∈ ctxU t tau x₁ x₂ lam := (Subgroup.mem_inf.mp hbCS).1
  have hbN : b ∈ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hb).2
  rw [← hD.E0_eq]
  exact ⟨hbU, hbN⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
