module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.Coordinator.CaseSplit
public import CFSG.HardMathSupport.Solomon.Proving.Basic
public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

theorem prop41_of_inputs (h21 : Prop21) (h22 : Prop22) (h31 : Lemma31) : Prop41 := by
  intro G _ _ m p hS
  have hp3 : 3 ≤ p := by
    have h2 := hS.prime.two_le
    have h3 := hS.ne_two
    omega
  refine ⟨?_, cases_of_caseOne_of_five_lt hS fun hp5 => ?_⟩
  · obtain ⟨B, hB0, hw⟩ := h22 G m p hS
    exact ⟨B, CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax hp3 hB0,
      (h21 G m p hS B hB0.1).1, hw⟩
  · obtain ⟨B, hB0⟩ :=
      CFSG.HardMathSupport.Solomon.Proving.exists_isBZeroMax_of_not_glaDeltaZero hS.not_deltaZero
    have hB1 := CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax hp3 hB0
    have hsc := lemma23_proved G m p hS B hB1
    exact ⟨B, hB1, (h21 G m p hS B hB0.1).2 hp5,
      lambdaStarGroup_eq_psiStarGroup_of_five_lt h31 hS hp5 hB0.1 hsc⟩

end CFSG.HardMathSupport.Solomon.LocalBalance
