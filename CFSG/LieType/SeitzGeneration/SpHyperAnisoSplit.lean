module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.HyperReducible
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration

@[expose] def IsSpTwoThree (d : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), q.p = 2 ∧ q.exponent = 1 ∧
    (d.1 = .B r q ∨ d.1 = .C r q)

end CFSG.LieType.SeitzGeneration
