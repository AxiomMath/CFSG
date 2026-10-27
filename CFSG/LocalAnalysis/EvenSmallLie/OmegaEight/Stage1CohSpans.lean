module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1CohData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def CertSpans (n m p : ℕ) (R Bcols : Array ℕ) : Prop :=
  ∀ c : Fin n → ZMod 2, Matrix.mulVec (toMat p n R) c = 0 →
    ∃ e : Fin m → ZMod 2, c = Matrix.mulVec (toMat m n Bcols).transpose e

@[expose] def gamSpans (ε : Eps) : Prop :=
  CertSpans (7 * 36) 6 (48 * 36) (linBits (7 * 36) (48 * 36) (gamFb ε))
    (Array.ofFn (n := 6) fun m => gamSol ε m)

@[expose] def extSpans (ε : Eps) : Prop :=
  CertSpans (6 * 36) 36 (nRels ε * 36) (linBits (6 * 36) (nRels ε * 36) (extFb ε))
    (Array.ofFn (n := 36) fun j => cobFb6 ε (2 ^ (j : ℕ)))

end CFSG.EvenSmallLie.OmegaEight.Stage1
