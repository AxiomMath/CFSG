module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d6a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_card_L_eq_mul (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) :
    Nat.card ↥(q13L t tau x₁ x₂ rho om)
      = (conjIn (q13L t tau x₁ x₂ rho om) t).ncard * (3 * 2 ^ 7) := by
  rw [card_eq_ncard_conjIn_mul (q13L t tau x₁ x₂ rho om) t,
    q13d_CL_t h hB, q13d_card_CM_t h]

theorem q13d_ncard_tL_le (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    (conjIn (q13L t tau x₁ x₂ rho om) t).ncard ≤ 2 ^ 6 := by
  have hsub : conjIn (q13L t tau x₁ x₂ rho om) t ⊆
      t • (q13P t tau x₁ x₂ rho om : Set G) := by
    rintro u ⟨g, hg, rfl⟩
    exact q13d_tL h hII g hg
  calc (conjIn (q13L t tau x₁ x₂ rho om) t).ncard
      ≤ (t • (q13P t tau x₁ x₂ rho om : Set G)).ncard := Set.ncard_le_ncard hsub
    _ = (q13P t tau x₁ x₂ rho om : Set G).ncard := Set.ncard_smul_set t _
    _ = Nat.card ↥(q13P t tau x₁ x₂ rho om) :=
        (Nat.card_coe_set_eq (q13P t tau x₁ x₂ rho om : Set G)).symm
    _ = 2 ^ 6 := q13d_card_P h hII

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
