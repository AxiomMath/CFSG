module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

@[expose] def CoverThreeIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (∃ q, d.1 = .A 2 q ∧ 3 ∣ q.card - 1) ∨ (∃ q, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1)

@[expose] def CoverThreeNine (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (∃ q, d.1 = .A 2 q ∧ 9 ∣ q.card - 1) ∨ (∃ q, d.1 = .twistedA 2 q ∧ 9 ∣ q.card + 1)

@[expose] def IsUThreeEight (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .twistedA 2 q

end CFSG.HardMathSupport.Foote.Coordinator
