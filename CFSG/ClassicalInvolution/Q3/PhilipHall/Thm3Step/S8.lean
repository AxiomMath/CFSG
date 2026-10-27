module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S8Datum
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf50CaseITG

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

section Step


theorem thm3RStdSimple_of_caseII
    (h2 : FrameCaseIITGN) (m : ℕ) : Thm3RStdSimple m := by
  intro Y _ _ _ hY hih K hΦ hA
  obtain ⟨J, zK, zJ, a, g, hD, hv, ha, hac, hne, hg, hgz⟩ := S8.exists_frameData hΦ hA
  have hnab : ∃ a b : Y, a * b ≠ b * a := S8.nonabelian hΦ.hyp
  have hT : Thm3RBelowG (Nat.card Y) := by
    rw [hY]
    exact hih.below
  have hB : CIT3Below (Nat.card Y) := CIT3Below.mono (by omega) hih.cit
  have hP : TL4.TightBelowRPlus 3 (Nat.card Y) := hih.pkg.mono (by omega)
  by_cases hs : aStar (CoreAssembly.conjClass K) K = CoreAssembly.conjClass K
  · exact h2 Y hT hnab hB hP K zK hD J zK zJ a g hv ha hac hne hg hgz hs
  · exact frameCaseITGN_proved Y hT hnab hB hP K zK hD J zK zJ hv hs

end Step

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
