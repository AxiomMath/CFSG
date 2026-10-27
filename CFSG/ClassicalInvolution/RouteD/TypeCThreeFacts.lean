module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeFactsOrthTags
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeBridgeFacts

public section

namespace CFSG.ClassicalInvolution.RouteD.LieBridge

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem fundamentalCentralizerNotSolvable (p : ℕ) [Fact p.Prime] :
    FundamentalCentralizerNotSolvable p := by
  intro hp2 t n e hfund hadm h4 h1 h2
  refine not_solvable_of_partner hp2 hfund hadm h4 ?_
  cases t with
  | PSL =>
    have hn : 2 ≤ n := hadm.2.2.1
    exact partner_PSL hadm (by by_contra h; exact h1 ⟨rfl, by omega⟩)
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    exact partner_PSU hadm (by by_contra h; exact h2 ⟨rfl, by omega⟩)
  | PSp => exact partner_PSp hadm
  | POmegaOdd => exact partner_POmegaOdd hadm
  | POmegaPlus => exact partner_POmegaPlus hadm
  | POmegaMinus => exact partner_POmegaMinus hadm
  | G2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    exact partner_G2 hadm
  | F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact partner_F4 hadm
  | E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact partner_E6 hadm
  | E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact partner_E7 hadm
  | E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact partner_E8 hadm
  | twistedE6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact partner_twistedE6 hadm
  | trialityD4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact partner_trialityD4 hadm
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact hfund.elim

end CFSG.ClassicalInvolution.RouteD.LieBridge
