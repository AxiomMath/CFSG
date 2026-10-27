module

public import CFSG.GroupTheory.SylowIntersectionControl.CharPair

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin

variable {Ω : Type} [Group Ω]

structure IsGomiSingularSubgroup (G S X : Subgroup Ω) : Prop where
  le : X ≤ G
  eq_commutator_thompsonJ : X = ⁅X, thompsonJ S⁆
  twoResidual_eq : twoResidual X = X
  commutator_pCoreOf_le : ⁅pCoreOf 2 G, X⁆ ≤ gomiV G
  natural : ∃ (C : Subgroup Ω) (n : ℕ), 1 ≤ n ∧
    IsNatL2Section X C ⁅gomiV G, X⁆ (⁅gomiV G, X⁆ ⊓ Subgroup.centralizer (X : Set Ω)) n

end CFSG.GroupTheory
