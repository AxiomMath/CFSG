module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

@[expose] def IdxSplit (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A _ q | .twistedA _ q | .B _ q | .D _ q | .twistedD _ q | .G2 q => q.p = 2 ∧ p ∣ q.card - 1
  | _ => False

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
