module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.RootData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open Heis

@[expose] def R1negRoots : Set (Fin Tag.F4.rank → ℤ) := {-alpha1, -root1342, -theta}

@[expose] def pureNegRoots1 : Set (Fin Tag.F4.rank → ℤ) := {-alpha1, -theta}

@[expose] def pureNegRoots2 : Set (Fin Tag.F4.rank → ℤ) := {-root1342, -theta}

theorem theta_add_deg_neg_one : ∀ β ∈ rootFinset .F4, β 0 = -1 → theta + β ∈ rootFinset .F4 := by
  decide +kernel


abbrev R1neg (K : Type) [Field K] : Subgroup (ModGL Tag.F4 K) := rootSpan Tag.F4 K R1negRoots

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
