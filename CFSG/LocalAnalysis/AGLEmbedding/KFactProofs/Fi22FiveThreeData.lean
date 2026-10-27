module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

set_option compiler.extract_closed false

@[expose] def e9W1 : List Int :=
  [1, 1, 1, -2, 1, 2, 1, 2, -1, -1, -1, -2, -2, -2, -2, 1, -2, -2, 1, 2, -1, -1, -1, -1, -1,
   2, 1, 1, -2, 1, -2, 1, 2, -1, -1, -1, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2]

@[expose] def e9W2 : List Int :=
  [-2, -2, 1, 2, -1, -2, 1, 1, 2, 1, 1, 1, -2, -2, -1, 2, -1, 2, 2, 2, 1, -2, 1, 2, -1, 2,
   -1, 2, -1, -2, -2, -2, -1, -2, 1, 1, 1, 1, 1, -2, -1, -2, -2, -2, -2, -2, -2, -2, -2]

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
