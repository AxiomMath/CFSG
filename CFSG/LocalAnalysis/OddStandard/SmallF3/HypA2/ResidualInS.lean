module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ResidualInA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ResidualInB
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem inS_of_isResidualA2 (hL : ResidualNotChevOdd) (hA8 : A8NotL34) (hO : SporadicOrders)
    (hG : G2FourOrder) {K : Type} [Group K] [Finite K] (hR : IsResidualA2 K) :
    InS (K ⧸ center K) := by
  rcases hR with ⟨hc, hm⟩ | ⟨m, hm, hc, ⟨e⟩⟩ | h | h | h | h | h | h
  · exact Or.inr (inSB_of_psl_two_three_eight (LieModel.quotient_center hc hm))
  · refine Or.inl (inSA_of_alternating (n := 2 * m) hL hA8 hO (by omega) ?_)
    exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e
  · exact Or.inl (inSA_of_hs hL hO h)
  · exact Or.inl (inSA_of_evenLie hL hO hG (Or.inl h))
  · exact Or.inl (inSA_of_evenLie hL hO hG (Or.inr (Or.inl h)))
  · exact Or.inl (inSA_of_evenLie hL hO hG (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (inSA_of_evenLie hL hO hG (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (inSA_of_evenLie hL hO hG (Or.inr (Or.inr (Or.inr (Or.inr h)))))

end CFSG.OddStandard.SmallF3.HypA2
