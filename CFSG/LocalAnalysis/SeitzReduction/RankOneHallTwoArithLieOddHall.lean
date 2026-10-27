module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithAltSpor
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOdd

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem eq_psl_two_seven_of_hallTwoArith_lie_odd {t : StatedLieTag} {m p f c : ℕ}
    (hadm : StatedLieAdmissible t m p f) (hp2 : p ≠ 2)
    (hc : c * lieOrderDivisor t m (p ^ f) = lieOrderNumerator t m (p ^ f))
    (hT : HallTwoArith c) : t = .PSL ∧ m = 2 ∧ p = 7 ∧ f = 1 := by
  obtain ⟨e, h, he1, rfl, -, hdiv⟩ := hT
  exact LieOdd.eq_psl_two_seven_of_lie_odd hadm hp2 hc.symm he1 hdiv

theorem eq_psl_two_seven_of_hallTwoArith_card {X : Type} [Group X] {t : StatedLieTag}
    {m p f : ℕ} (hLie : LieOrderFormulasInput) (hadm : StatedLieAdmissible t m p f)
    (hp2 : p ≠ 2) (hX : Blueprint.LieModel X t m p f) (hT : HallTwoArith (Nat.card X)) :
    t = .PSL ∧ m = 2 ∧ p = 7 ∧ f = 1 :=
  eq_psl_two_seven_of_hallTwoArith_lie_odd hadm hp2 (hLie X t m p f hadm hX).2.1 hT

end CFSG.SeitzReduction.RankOne
