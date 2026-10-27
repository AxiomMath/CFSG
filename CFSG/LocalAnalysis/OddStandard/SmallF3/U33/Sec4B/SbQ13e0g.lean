module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS25
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_no_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, ∀ p ∈ q13P t tau x₁ x₂ rho om, g * g ≠ t * p := by
  intro g hgL p hp hgg_eq
  obtain ⟨e⟩ := hD.P_iso
  have hg : g ∈ normalizer ((q13P t tau x₁ x₂ rho om : Subgroup G) : Set G) :=
    q13d_normalizer_le_of_charIn hD.P_char.1 hgL
  have ht : t ∈ normalizer ((q13P t tau x₁ x₂ rho om : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun n hn => by
      rw [hD.t_inv_P n hn]
      exact inv_mem hn
  let σ : MulAut ↥(q13P t tau x₁ x₂ rho om) := Outside.conjAut _ g hg
  let τ₀ : MulAut ↥(q13P t tau x₁ x₂ rho om) := Outside.conjAut _ t ht
  have hsig : σ * σ = τ₀ := by
    change Outside.conjAut (q13P t tau x₁ x₂ rho om) g hg *
        Outside.conjAut (q13P t tau x₁ x₂ rho om) g hg =
      Outside.conjAut (q13P t tau x₁ x₂ rho om) t ht
    ext x
    rw [MulAut.mul_apply, Outside.conjAut_coe, Outside.conjAut_coe, Outside.conjAut_coe]
    have hpx' : p * (x : G) * p⁻¹ = (x : G) := by
      rw [q13d_P_comm h hD.A_cent p hp x x.2, mul_assoc, mul_inv_cancel, mul_one]
    rw [show g * (g * (x : G) * g⁻¹) * g⁻¹ = (g * g) * (x : G) * (g * g)⁻¹ by group,
      hgg_eq,
      show (t * p) * (x : G) * (t * p)⁻¹ = t * (p * (x : G) * p⁻¹) * t⁻¹ by group,
      hpx']
  have htinv : ∀ b : ↥(q13P t tau x₁ x₂ rho om), τ₀ b = b⁻¹ := by
    intro b
    apply Subtype.ext
    change t * (b : G) * t⁻¹ = ((b⁻¹ : ↥(q13P t tau x₁ x₂ rho om)) : G)
    rw [Subgroup.coe_inv]
    exact hD.t_inv_P b b.2
  exact (Outside.HS25 e τ₀ σ htinv) hsig

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
