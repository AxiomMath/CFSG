module

public import CFSG.GroupTheory.IsCyclicOfPRankLeOne

public section

namespace CFSG

theorem isCyclic_of_le_of_pRank_le_one {X : Type} [Group X] [Finite X] {p : Nat} (hp : p.Prime)
    (hp2 : p ≠ 2) {S N : Subgroup X} (hSp : IsPGroup p S) (hSN : S ≤ N)
    (hN : CFSG.Open.pRank p N ≤ 1) : IsCyclic ↥S := by
  have hS : CFSG.Open.pRank p (⊤ : Subgroup ↥S) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup S]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt hSN).trans hN
  exact CFSG.isCyclic_of_pRank_le_one hp hp2 hSp hS

end CFSG

end
