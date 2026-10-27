module

public import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne

public section

namespace CFSG

theorem all_pSubgroups_isCyclic_of_pRank_le_one {X : Type} [Group X] [Finite X] {p : Nat}
    (hp : p.Prime) (hp2 : p ≠ 2) {N : Subgroup X} (hN : CFSG.Open.pRank p N ≤ 1) :
    ∀ S : Subgroup X, S ≤ N → IsPGroup p S → IsCyclic ↥S := by
  intro S hSN hSp
  exact isCyclic_of_le_of_pRank_le_one hp hp2 hSp hSN hN

end CFSG

end
