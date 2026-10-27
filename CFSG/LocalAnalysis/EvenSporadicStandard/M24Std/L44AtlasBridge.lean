module

public import CFSG.RankThree.PartTwo.KFacts.KS21L44

public noncomputable section

namespace CFSG.EvenSporadicStandard.M24Std

namespace L44Atlas

open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial

@[expose] def pslEquivProjectiveSL (n : ℕ) (K : Type*) [Field K] :
    PSL(n, K) ≃* LinearFlag.projectiveSL n K :=
  QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center n K).symm

@[expose] def pslFourEquivSL :
    PSL(4, GaloisField 2 2) ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2) :=
  (QuotientGroup.quotientMulEquivOfEq CFSG.RankThree.PartTwo.KFacts.KS21.L44.center_M).trans
    QuotientGroup.quotientBot

end L44Atlas

end CFSG.EvenSporadicStandard.M24Std
