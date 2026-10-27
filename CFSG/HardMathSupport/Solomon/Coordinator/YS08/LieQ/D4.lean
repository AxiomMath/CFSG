module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Tag
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.Open.StatedDefs
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLift
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false

section D4


theorem radRigid_POmegaPlus_four {F : Type} [Field F] [Finite F] [CharP F 2] :
    RadRigid 2 (StatedProj (StatedOmega (StatedQuadPlus 4 F))) := by
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  exact (radRigid_adjointGroup (τ := Tag.D4) (K := F) (by decide)).of_mulEquiv e.symm

end D4

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
