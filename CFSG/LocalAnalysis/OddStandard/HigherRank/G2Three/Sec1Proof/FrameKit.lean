module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Frame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabOps4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabOps1

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup

structure FIdx where
  a1 : ℕ
  b1 : ℕ
  a2 : ℕ
  b2 : ℕ
  h0 : ℕ
  sg : ℕ
  u1 : ℕ
  u2 : ℕ

variable {Γ : Type} [Group Γ] {D : TabData} {elt : ℕ → Γ}

@[expose] def ml (D : TabData) (l : List ℕ) : ℕ := l.foldl D.mul 0

variable {fr : SFrame Γ} {I : FIdx}

variable {gr : Frame Γ}

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
