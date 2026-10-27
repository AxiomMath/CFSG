module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.HardMathSupport.Solomon.Coordinator

theorem map_fixSubgroup {K L : Type*} [Group K] [Group L] (e : K ≃* L) (α : MulAut K) :
    (fixSubgroup α).map e.toMonoidHom = fixSubgroup (e.symm.trans (α.trans e)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show (e.symm.trans (α.trans e)) (e x) = e x
    have hx' : α x = x := by simpa using (mem_fixSubgroup.mp hx)
    simpa using congrArg e hx'
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    show α (e.symm y) = e.symm y
    have hy0 : (e.symm.trans (α.trans e)) y = y := by simpa using (mem_fixSubgroup.mp hy)
    have hy' : e (α (e.symm y)) = y := by simpa using hy0
    apply e.injective
    rw [hy', e.apply_symm_apply]

end CFSG.LocalAnalysis.GLTheoremA
