module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.ClassicalModelStatedBridge

@[expose] def standardTypeOmegaMinusEquiv (m : ℕ) (K : Type) [Field K] (b c : K) :
    LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus (m + 1) K b c)) :=
  (CFSG.Open.StatedAPI.mapMkEquivStatedProj
    (LargeEvenOmega (LargeEvenQMinus m b c))).symm.trans
      (omegaModelEquivOfReindex (Equiv.sumAssoc (Fin m) (Fin m) (Fin 2))
        (Q := LargeEvenQMinus m b c) (Q' := StatedQuadMinus (m + 1) K b c)
        fun _ => rfl)

end CFSG.LieType.SeitzGeneration
