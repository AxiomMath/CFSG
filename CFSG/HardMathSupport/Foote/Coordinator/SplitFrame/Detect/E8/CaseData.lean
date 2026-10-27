module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs
public import CFSG.LieType.Chevalley.RootWeightFiltration
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open Heis

@[expose] def R1negRoots : Set (Fin Tag.E8.rank → ℤ) :=
  {β | IsRoot Tag.E8 β ∧ β 4 % 5 = 0 ∧ β 7 < 0}


abbrev R1neg (K : Type) [Field K] : Subgroup (ModGL Tag.E8 K) := rootSpan Tag.E8 K R1negRoots

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
