module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBPSL
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBPSp
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBPSU
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBPOmegaMinus
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBPOmegaPlus
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBPOmegaOdd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBF4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBG2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBE6
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBE7
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBE8
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBTwistedG2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBTwistedF4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBTrialityD4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBTwistedE6
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSuzuki

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag)

theorem fixedLowerBoundAt_all
    (t : StatedLieTag) : FixedLowerBoundAt t := by
  cases t with
  | PSL => exact fixedLowerBoundAt_PSL
  | PSU => exact fixedLowerBoundAt_PSU
  | PSp => exact fixedLowerBoundAt_PSp
  | POmegaOdd => exact fixedLowerBoundAt_POmegaOdd
  | POmegaPlus => exact fixedLowerBoundAt_POmegaPlus
  | POmegaMinus => exact fixedLowerBoundAt_POmegaMinus
  | G2 => exact fixedLowerBoundAt_G2
  | F4 => exact fixedLowerBoundAt_F4
  | E6 => exact fixedLowerBoundAt_E6
  | E7 => exact fixedLowerBoundAt_E7
  | E8 => exact fixedLowerBoundAt_E8
  | twistedE6 => exact fixedLowerBoundAt_twistedE6
  | trialityD4 => exact fixedLowerBoundAt_trialityD4
  | twistedB2 => exact fixedLowerBoundAt_twistedB2
  | twistedG2 => exact fixedLowerBoundAt_twistedG2
  | twistedF4 => exact fixedLowerBoundAt_twistedF4
  | Tits => exact fun K _ _ n ℓ f f₀ p _ _ ht => absurd rfl ht

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
