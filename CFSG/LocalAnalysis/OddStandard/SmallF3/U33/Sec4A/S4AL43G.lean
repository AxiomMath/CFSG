module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43F

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem lemma4_3_of (hI : Sec4Inputs) (hG : Sec4Glob G) (h : Ctx t L S x₁ x₂ lam rho tau)
    (h2 : Lemma4_2Concl S) : Lemma4_3Concl t := by
  rcases card_twoCore_cases h.hyp with h2c | h4 | h8
  · exact twoCore_eq_zpowers_of_card_eq_two h.hyp h2c
  · exact (false_of_card_eq_four hI hG h h2 h4).elim
  · exact (false_of_eight_le_card h h2 h8).elim

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
