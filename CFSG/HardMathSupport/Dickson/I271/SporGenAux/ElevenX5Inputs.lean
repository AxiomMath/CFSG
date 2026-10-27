module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.Gen11

@[expose] def elevenX5yCheck (_ : Unit) : Bool :=
  agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) (gen11W1 ++ gen11W4)
    (gen11W4 ++ powL 3 gen11W1)

end CFSG.HardMathSupport.Dickson.I271
