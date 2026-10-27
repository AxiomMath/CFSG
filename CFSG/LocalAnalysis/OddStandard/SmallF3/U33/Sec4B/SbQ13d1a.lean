module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_card_AC (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(q13A t tau x₁ x₂ rho ⊔ closure ({t, om} : Set G)) = 2 ^ 7 := by
  have hK : ∀ k ∈ closure ({t, om} : Set G), ∀ a ∈ q13A t tau x₁ x₂ rho,
      k * a * k⁻¹ ∈ q13A t tau x₁ x₂ rho := q13d_CO_norm_A h
  have hHK : q13A t tau x₁ x₂ rho ⊓ closure ({t, om} : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    exact q13d_A_inf_CO h g hg.1 hg.2
  rw [card_sup_eq_mul hK hHK, q13a_card_A h, q13d_card_CO h]
  norm_num

theorem q13d_AC_le_cent (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13A t tau x₁ x₂ rho ⊔ closure ({t, om} : Set G) ≤ ctxU t tau x₁ x₂ lam
      ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) := by
  refine le_inf (sup_le (q13d_A_le_U h) (q13d_CO_le_U h)) ?_
  refine sup_le ?_ ?_
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (q13d_A_cent_N h a ha n hn).symm
  · intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (q13d_CO_cent_N h c hc n hn).symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
