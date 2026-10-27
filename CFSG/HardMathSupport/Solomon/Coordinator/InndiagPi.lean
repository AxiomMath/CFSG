module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofInndiag

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec14
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

theorem inndiagPi_true_eq_innAutDerived (q : ℕ) (K : Type) [Field K] [Finite K] :
    inndiagPi true q K = innAutDerived (projImage (slPi true 3 q K)) := by
  rw [← comap_stdPinnedPSL_three_inndiag_eq K (pslEquivProjective q K)]
  ext β
  rw [PinnedAut.mem_comap_inndiag, stdPinnedPSL_inndiag]
  exact Proof142Res.mem_inndiagPi_true_iff β

theorem inndiagPi_false_eq_innAutDerived {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    inndiagPi false (p ^ f) K = innAutDerived (projImage (slPi false 3 (p ^ f) K)) := by
  rw [← comap_stdPinnedPSU3_inndiag_eq h hq (psuEquivUnitary h)]
  ext β
  rw [PinnedAut.mem_comap_inndiag]
  exact Proof142Res.mem_inndiagPi_false_iff h β

end CFSG.HardMathSupport.Solomon.Coordinator
