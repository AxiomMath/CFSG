module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e5a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e5b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_card_B_eq (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    Nat.card (q13B t tau x₁ x₂ rho om) = 2 ^ 9 := by
  have hcard := q13e_card_B h hB hD
  have hne := q13e_card_B_ne h hB hD
  have hle := q13e_card_B_le h hB hC hD
  rcases hcard with h8 | h9 | h10
  · exact absurd h8 hne
  · exact h9
  · exfalso
    rw [h10] at hle
    norm_num at hle

theorem q13e_kap_mem_AN (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, ⁅t, b⁆ ∈ q13AN t tau x₁ x₂ rho := by
  exact q13e_kap_mem_AN_of_card_le h hB hD (le_of_eq (q13e_card_B_eq h hB hC hD))

theorem q13e_B_sq_mem_P (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, b * b ∈ q13P t tau x₁ x₂ rho om := by
  intro b hb
  have h1 := q13e_sq_mem_CLP h hD b hb
  rwa [q13e_CLP_eq_P h hB hC hD] at h1

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
