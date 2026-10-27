module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieTitsSz
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU3
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

@[expose] def KDLieRowsRest : Prop :=
  KDLieRowSp4Eight ∧ KDLieRowSp6Two ∧ KDLieRowOmega8PlusTwo ∧ KDLieRowG2Eight ∧ KDLieRowU4Eight ∧
    KDLieRowU6Two ∧ KDLieRowTD4Two ∧ KDLieRowReeF4EightThree ∧ KDLieRowReeF4ThirtyTwoFive

section Certs

theorem kdLieRowsOpen_of_rest
    (h : KDLieRowsRest) : KDLieRowsOpen := by
  obtain ⟨hSp4, hSp6, hOm8, hG2, hU4, hU6, hTD4, hR8, hR32⟩ := h
  exact ⟨hSp4, hSp6, hOm8, hG2, hU4, kdLieRowU5Two_holds, hU6, hTD4, kdLieRowTitsThree_holds, hR8,
    kdLieRowTitsFive_holds, hR32, kdLieRowSzFive_holds⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA
