module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTSL
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTSU
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTSp
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTOrth
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTExc
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTExcE67

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution.Generic

section Cheap


theorem lie3At_G2 (n : ℕ) : Lie3At .G2 n :=
  lie3At_of_survivor (Or.inr (Or.inr rfl))

theorem lie3At_of_not_fund {τ : StatedLieTag} (h : ¬ IsFundTag τ) (n : ℕ) : Lie3At τ n :=
  fun hf => absurd hf h

theorem lie3At_of_admissible_zero {τ : StatedLieTag}
    (hτ : ∀ n, StatedLieAdmissible τ n 3 1 → n = 0) (h : Lie3At τ 0) (n : ℕ) : Lie3At τ n := by
  by_cases hn : n = 0
  · subst hn
    exact h
  · intro _ ha
    exact absurd (hτ n ha) hn

end Cheap

section Rows


theorem lie3At_POmegaOdd (n : ℕ) : Lie3At .POmegaOdd n := by
  by_cases hn : 3 ≤ n
  · exact lie3At_of_kill (by decide) (by decide) (kill3At_POmegaOdd n hn)
  · intro _ ha
    exact absurd ha.2.2.1 hn

theorem lie3At_POmegaPlus (n : ℕ) : Lie3At .POmegaPlus n := by
  by_cases hn : 4 ≤ n
  · exact lie3At_of_kill (by decide) (by decide) (kill3At_POmegaPlus n hn)
  · intro _ ha
    exact absurd ha.2.2 hn

theorem lie3At_POmegaMinus (n : ℕ) : Lie3At .POmegaMinus n := by
  by_cases hn : 4 ≤ n
  · exact lie3At_of_kill (by decide) (by decide) (kill3At_POmegaMinus n hn)
  · intro _ ha
    exact absurd ha.2.2 hn

theorem lie3At_F4 (n : ℕ) : Lie3At .F4 n :=
  lie3At_of_admissible_zero (fun _ ha => ha.2.2)
    (lie3At_of_kill (by decide) (by decide) kill3At_F4) n

theorem lie3At_E6 (n : ℕ) : Lie3At .E6 n :=
  lie3At_of_admissible_zero (fun _ ha => ha.2.2)
    (lie3At_of_kill (by decide) (by decide) kill3At_E6) n

theorem lie3At_E7 (n : ℕ) : Lie3At .E7 n :=
  lie3At_of_admissible_zero (fun _ ha => ha.2.2)
    (lie3At_of_kill (by decide) (by decide) kill3At_E7) n

theorem lie3At_E8 (n : ℕ) : Lie3At .E8 n :=
  lie3At_of_admissible_zero (fun _ ha => ha.2.2)
    (lie3At_of_kill (by decide) (by decide) kill3At_E8) n

theorem lie3At_twistedE6_of_zero (h : Lie3At .twistedE6 0) (n : ℕ) : Lie3At .twistedE6 n :=
  lie3At_of_admissible_zero (fun _ ha => ha.2.2) h n

theorem lie3At_trialityD4_of_zero (h : Lie3At .trialityD4 0) (n : ℕ) : Lie3At .trialityD4 n :=
  lie3At_of_admissible_zero (fun _ ha => ha.2.2) h n

theorem lie3Table_of_rows (hTw : Lie3At .twistedE6 0) (hD4 : Lie3At .trialityD4 0) :
    Lie3Table := by
  refine lie3Table_of_at fun τ n => ?_
  cases τ with
  | PSL => exact lie3At_PSL n
  | PSU => exact lie3At_PSU n
  | PSp => exact lie3At_PSp n
  | POmegaOdd => exact lie3At_POmegaOdd n
  | POmegaPlus => exact lie3At_POmegaPlus n
  | POmegaMinus => exact lie3At_POmegaMinus n
  | G2 => exact lie3At_G2 n
  | F4 => exact lie3At_F4 n
  | E6 => exact lie3At_E6 n
  | E7 => exact lie3At_E7 n
  | E8 => exact lie3At_E8 n
  | twistedE6 => exact lie3At_twistedE6_of_zero hTw n
  | trialityD4 => exact lie3At_trialityD4_of_zero hD4 n
  | twistedB2 => exact lie3At_of_not_fund (by simp [IsFundTag]) n
  | twistedG2 => exact lie3At_of_not_fund (by simp [IsFundTag]) n
  | twistedF4 => exact lie3At_of_not_fund (by simp [IsFundTag]) n
  | Tits => exact lie3At_of_not_fund (by simp [IsFundTag]) n

end Rows

end CFSG.CGT.PushingUpLit.SolKNA
