module

public import Certificates.Data.M13L33
public import CFSG.Certificates.Kernel.KDenseP.HeSeven.Pairs

public section

namespace CFSG.KC.KDenseP.L33

open CFSG.AGLEmbedding.Norton.MON11_13 CFSG.HardMathSupport.Dickson.BMRows.M13L33
  CFSG.KC.KDenseP.HeSeven

@[expose] def e17632 : Prs :=
  [(yW ++ yIW, []), (thirteenX ++ yW, yW ++ thirteenX)] ++ l33Rels.map fun r => (relW r, [])

end CFSG.KC.KDenseP.L33

end
