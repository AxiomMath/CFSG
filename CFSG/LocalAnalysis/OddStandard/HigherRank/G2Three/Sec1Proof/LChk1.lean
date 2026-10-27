module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.FrameKit

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open Subgroup

@[expose] def idx1 (D : TabData) : FIdx :=
  ⟨ml D [1, 2, 2, 2, D.inv 1], 2, ml D [3, 4, 4, 4, D.inv 3], 4, 5, 6, 1, 3⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
