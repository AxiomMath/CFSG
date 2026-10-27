module

public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectExc
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectPSU

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank

theorem fundPerfect_core (t : StatedLieTag) (n p e : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, R ≤ ⁅R, R⁆ := by
  cases t with
  | PSL =>
    by_cases hn : n = 2
    · subst hn
      exact fundPerfect_PSL_two p e hadm h4
    · exact fundPerfect_PSL n p e h4 hadm (by have := hadm.2.2.1; omega)
  | PSU => exact fundPerfect_PSU n e hp2 hadm h4
  | PSp => exact fundPerfect_PSp n p e hadm h4
  | POmegaOdd => exact fundPerfect_POmegaOdd n p e h4 hadm
  | POmegaPlus => exact fundPerfect_POmegaPlus n p e h4 hadm
  | POmegaMinus => exact fundPerfect_POmegaMinus_any n p e hadm h4
  | G2 => exact fundPerfect_G2 n p e hadm h4
  | F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact fundPerfect_F4 p e h4 hadm
  | E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact fundPerfect_E6 p e h4 hadm
  | E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact fundPerfect_E7 p e h4 hadm
  | E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact fundPerfect_E8 p e h4 hadm
  | twistedE6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact fundPerfect_twistedE6 p e hadm h4
  | trialityD4 => exact fundPerfect_trialityD4 n p e hadm h4
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd hfund (by simp [IsFundTag])

end CFSG.ClassicalInvolution.ModelFacts
