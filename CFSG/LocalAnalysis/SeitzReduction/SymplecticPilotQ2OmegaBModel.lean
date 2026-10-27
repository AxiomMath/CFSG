module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaSpA

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def SpATwoTorusInput : Prop :=
  ∀ (N j : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 2 ≤ j → 2 * j ≤ N →
    ∀ S : Subgroup (StatedSp N K), S ≤ centralizer ({spARep N j} : Set (StatedSp N K)) →
      Nat.card S = 3 →
      ∃ P : Subgroup (StatedSp N K), ⁅P, P⁆ = P ∧ P ≤ centralizer (S : Set (StatedSp N K)) ∧
        ¬ P ≤ centralizer ({spARep N j} : Set (StatedSp N K))

end CFSG.SeitzReduction.SymplecticPilot
