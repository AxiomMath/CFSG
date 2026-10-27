module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup

@[expose] def InvolutionCentralizerNotTwoGroup (t : Assembly.LowTwoRank.StatedLieTag) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (f : ℕ), Blueprint.ChevalleyExceptionalModel Y t 2 f →
    IsSimpleGroup Y → ∀ c : Y, orderOf c = 2 → ¬ IsPGroup 2 ↥(centralizer ({c} : Set Y))

end CFSG.ComponentClassification.HarrisLit.L33.E2
