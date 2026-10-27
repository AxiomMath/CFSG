module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFus

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzr_exists_conj_t_mul [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) {z : G} (hz : z ∈ fourGrp x₁ x₂) :
    ∃ n ∈ fzN2 t x₁ x₂, n * t * n⁻¹ = t * z :=
  fzl_exists_swap h hK hz

theorem fzr_conj_t_mem_W (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {g : G} (hw : g * t * g⁻¹ ∈ ctxW t x₁ x₂) :
    ∃ z ∈ fourGrp x₁ x₂, g * t * g⁻¹ = t * z := by
  have ht2 : t ^ 2 = 1 := (fzl_t_facts h).2.1
  have hw2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow (a := g) (b := t) (i := 2), ht2, mul_one, mul_inv_cancel]
  rcases fzl_invol_mem_W h hK hw hw2 with hZ | hz
  · exact absurd rfl (S4A.tG_inf_four_of_ctx h g _ hZ)
  · exact hz

end CFSG.OddStandard.SmallF3.FritzII
