module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Prog
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data
import CFSG.Certificates.Kernel.Common.StrLits

public section

set_option maxRecDepth 100000

namespace CFSG.KD.SLP.Gen11

open CFSG.KC.NortonSLPK CFSG.AGLEmbedding.Norton.Gen11

theorem parse_ok : parseEqB (decodeK (gen11Text0.toList ++ '\n' :: gen11Text1.toList)) S = true := by
  str_lits gen11Text0
  str_lits gen11Text1
  rw [String.toList_ofList, String.toList_ofList]
  quickRfl

end CFSG.KD.SLP.Gen11

end
