module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Statements
public import CFSG.LocalAnalysis.AGLEmbedding.GuestPrime

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open

structure AGLGlobal (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : IsKProper G
  charTwo : IsCharTwoType G
  rank : 3 ≤ evenRank G
  pre : GLBPreuniqueness G

export CFSG.AGLEmbedding (D1At)

variable {G : Type} [Group G] [Finite G]

theorem D2Global.toAGLGlobal (h : D2Global G) : AGLGlobal G :=
  ⟨h.simple, h.nonab, h.kProper, h.charTwo, le_trans (by norm_num) h.rank, h.preuniqueness⟩

theorem D1For.at (h : D1For G) {p : ℕ} (hp : p ∈ GLBBetaFour G) : D1At G p :=
  h p hp

end CFSG.AGLEmbeddingD2

namespace CFSG.AGLEmbedding

theorem D1Global.toAGLGlobal {G : Type} [Group G] [Finite G] (h : D1Global G) :
    CFSG.AGLEmbeddingD2.AGLGlobal G :=
  ⟨h.simple, h.nonab, h.kProper, h.charTwo, le_trans (by norm_num) h.rank, h.pre⟩

end CFSG.AGLEmbedding
