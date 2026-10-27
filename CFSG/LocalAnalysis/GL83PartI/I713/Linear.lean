module

public import CFSG.LocalAnalysis.GL83PartI.I713.LinearTwo
public import CFSG.LocalAnalysis.GL83PartI.I713.LinearHigher
public import CFSG.LocalAnalysis.GL83PartI.I713.LinearDiag
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace GL83.I713

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

theorem outClauseFor_projectiveSL (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) :
    OutClauseFor (LinearFlag.projectiveSL n K) := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · exact outClauseFor_projectiveSL_two K
  · exact outClauseFor_projectiveSL_of_diag hn3 fun p hp hp2 hpd =>
      two_le_pRank_projectiveSL_of_dvd hn3 hp hp2 hpd

theorem outClauseFor_classical_PSL {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (h : CFSG.Open.StatedClassicalModel S .PSL n p f) : OutClauseFor S := by
  obtain ⟨⟨-, -, hn, -, -⟩, K, _, _, -, ⟨eT⟩⟩ := h
  let e' : S ≃* LinearFlag.projectiveSL n K :=
    eT.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  exact OutClauseFor.of_mulEquiv e' (outClauseFor_projectiveSL K hn)

end GL83.I713
