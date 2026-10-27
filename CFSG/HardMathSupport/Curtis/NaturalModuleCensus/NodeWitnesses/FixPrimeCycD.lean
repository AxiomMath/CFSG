module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.Escapes

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses

open CFSG.AGLEmbedding

theorem fixPrimeCycTorus_d : FixPrimeCycTorus IdxD := by
  intro Y _ _ L J p u h hX
  exact (h.false_of_escapes
    (centralizerEscapes_of_isLieOfTorus_d hX h.prime h.five_le)).elim

theorem fixPrimeCycTorus_twistedD : FixPrimeCycTorus IdxTwistedD := by
  intro Y _ _ L J p u h hX
  exact (h.false_of_escapes
    (centralizerEscapes_of_isLieOfTorus_twistedD hX h.prime h.five_le)).elim

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses
