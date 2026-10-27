module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieTwoCard
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOddHall
public import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

private theorem classicalModel_of_lieModel_of_ne_zero {T : Type} [Group T] {t : StatedLieTag}
    {m p f : ℕ} (hm : m ≠ 0) (hT : Blueprint.LieModel T t m p f) :
    StatedClassicalModel T t m p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hm hT

theorem statedClassicalModel_of_lieModel_hallTwoArith (hLie : LieOrderFormulasInput)
    {T : Type} [Group T] {t : StatedLieTag} {m p f : ℕ} (hadm : StatedLieAdmissible t m p f)
    (hT : Blueprint.LieModel T t m p f) (H : HallTwoArith (Nat.card T)) :
    StatedClassicalModel T .PSL 3 2 1 ∧ Nat.card T = 168 := by
  obtain ⟨-, hmul, -⟩ := hLie T t m p f hadm hT
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨rfl, rfl, rfl⟩ := hallTwoArith_lie_two_of_mul_eq hadm hmul H
    refine ⟨classicalModel_of_lieModel_of_ne_zero (by norm_num) hT, ?_⟩
    rw [show lieOrderDivisor .PSL 3 (2 ^ 1) = 1 by decide,
      show lieOrderNumerator .PSL 3 (2 ^ 1) = 168 by decide, mul_one] at hmul
    exact hmul
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := eq_psl_two_seven_of_hallTwoArith_card hLie hadm hp2 hT H
    refine ⟨RankThree.PartTwo.Sec3.statedClassicalModel_psl_three_two_of_seven
      (classicalModel_of_lieModel_of_ne_zero (by norm_num) hT) (by norm_num), ?_⟩
    rw [show lieOrderDivisor .PSL 2 (7 ^ 1) = 2 by decide,
      show lieOrderNumerator .PSL 2 (7 ^ 1) = 336 by decide] at hmul
    omega

theorem eq_three_of_card_eq_168 {c e h : ℕ} (hc : c = 168) (hcard : c = 2 ^ e * h)
    (hh : Odd h) : e = 3 ∧ h = 21 :=
  two_pow_mul_odd_inj (e' := 3) (h' := 21) hh (by decide) (hcard.symm.trans hc)

end CFSG.SeitzReduction.RankOne
