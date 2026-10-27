module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3.Third

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

section Step


theorem thm3RTwoOrbit_of_rowFacts (hF : RowCentralizerFacts) (m : ℕ) : Thm3RTwoOrbit m := by
  intro Y _ _ Φ K hc htw
  have hC := thm3RConclG_twinOrbit hc.hyp hc.mem hc.notEmpty hc.inner htw 1
  rw [conjSub_one] at hC
  exact thm3RConclG_of_twinOrbit hc.hyp hc.mem hC fun L hL hLΔ M hM =>
    commutator_eq_bot_of_not_mem_twinOrbit hF hc.hyp hc.mem hc.notEmpty hc.inner htw hc.odd hL
      hLΔ hM

end Step

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3
