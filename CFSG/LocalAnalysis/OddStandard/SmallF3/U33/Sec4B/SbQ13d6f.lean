module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d6b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d6d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d6e2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_L_card (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    Nat.card ↥(q13L t tau x₁ x₂ rho om) = 3 * 2 ^ 11 ∨ Nat.card ↥(q13L t tau x₁ x₂ rho om)
      = 3 * 2 ^ 12 ∨
      Nat.card ↥(q13L t tau x₁ x₂ rho om) = 3 * 2 ^ 13 := by
  have hmul := q13d_card_L_eq_mul h hB
  have hle := q13d_ncard_tL_le h hII
  have hdvd := q13d_two_pow_dvd_card_L h hB
  have h3 := q13d_not_three_dvd_ncard_tL h hII
  generalize (conjIn (q13L t tau x₁ x₂ rho om) t).ncard = m at hmul hle h3
  rw [hmul] at hdvd ⊢
  norm_num at hdvd hle ⊢
  omega

theorem q13d_rho_syl3 (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    IsSylowIn 3 (zpowers rho) (q13L t tau x₁ x₂ rho om) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : zpowers rho ≤ q13L t tau x₁ x₂ rho om :=
    Subgroup.zpowers_le.mpr (q13d_rho_norm h)
  have hcardz : Nat.card ↥(zpowers rho) = 3 := by
    rw [Nat.card_zpowers, h.c11.ord_rho]
  refine ⟨hle, IsPGroup.of_card (n := 1) (by simpa using hcardz), ?_⟩
  have hidx := Subgroup.relIndex_mul_card (zpowers rho) (q13L t tau x₁ x₂ rho om)
  rw [inf_eq_left.mpr hle, hcardz] at hidx
  rcases q13d_L_card h hB hII with hc | hc | hc <;> rw [hc] at hidx <;> norm_num at hidx <;> omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
