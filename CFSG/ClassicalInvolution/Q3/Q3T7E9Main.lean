module

public import CFSG.ClassicalInvolution.Q3.Q3T7E9Base
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Dim4
public import CFSG.ClassicalInvolution.Q3.Q3T7E9OrthFinal
public import CFSG.ClassicalInvolution.RouteD.G2D4E189Rest
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.ClassicalInvolution.Q3.Q3ExcPinned
public import CFSG.ClassicalInvolution.Q3.Q3ExcTwE6
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E9

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77


theorem e189ModelAt_three_g2 (hadm : StatedLieAdmissible .G2 0 3 1) : E189ModelAt 3 1 .G2 0 :=
  G2D4Models.e189ModelAt_g2_odd (by norm_num) hadm

theorem e189ModelAt_three_td4 (hadm : StatedLieAdmissible .trialityD4 0 3 1) :
    E189ModelAt 3 1 .trialityD4 0 :=
  G2D4Models.e189ModelAt_of_noTwinsFund
    (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot (by norm_num)
      (Or.inr rfl) 0 hadm.2.1)
    (G2D4Models.noTwinsFund_td4 (by norm_num) hadm)

theorem e189ModelAt_three_all (t : StatedLieTag) (n : ℕ) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) : E189ModelAt 3 1 t n := by
  cases t with
  | PSL =>
    by_cases hn4 : n = 4
    · subst hn4
      exact e189ModelAt_three_psl_four
    · exact e189ModelAt_three_psl_of_ne_four hadm hn4
  | PSU =>
    by_cases hn4 : n = 4
    · subst hn4
      exact e189ModelAt_three_psu_four hadm
    · exact e189ModelAt_three_psu_of_ne_four hadm hn4
  | PSp =>
    by_cases hn2 : n = 2
    · subst hn2
      exact e189ModelAt_three_psp_two hadm
    · exact e189ModelAt_three_psp_of_ne_two hadm hn2
  | POmegaOdd => exact e189ModelAt_three_odd hadm
  | POmegaPlus => exact e189ModelAt_three_plus hadm
  | POmegaMinus => exact e189ModelAt_three_minus hadm
  | G2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    exact e189ModelAt_three_g2 hadm
  | F4 => exact e189ModelAt_three_exc (Or.inl rfl) hadm
  | E6 => exact e189ModelAt_three_exc (Or.inr (Or.inl rfl)) hadm
  | E7 => exact e189ModelAt_three_exc (Or.inr (Or.inr (Or.inl rfl))) hadm
  | E8 => exact e189ModelAt_three_exc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm
  | twistedE6 => exact e189ModelAt_three_exc (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hadm
  | trialityD4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact e189ModelAt_three_td4 hadm
  | twistedB2 => exact absurd hfund (by simp [IsFundTag])
  | twistedG2 => exact absurd hfund (by simp [IsFundTag])
  | twistedF4 => exact absurd hfund (by simp [IsFundTag])
  | Tits => exact absurd hfund (by simp [IsFundTag])

theorem e189ModelAt_three (t : StatedLieTag) (n : ℕ) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (_hG2 : t ≠ .G2) : E189ModelAt 3 1 t n :=
  e189ModelAt_three_all t n hfund hadm

end CFSG.ClassicalInvolution.Q3.Q3T7E9
