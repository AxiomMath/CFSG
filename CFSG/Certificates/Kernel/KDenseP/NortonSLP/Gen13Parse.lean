module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13Prog
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen13.Data
import CFSG.Certificates.Kernel.Common.StrLits

public section

set_option maxRecDepth 100000

namespace CFSG.KD.SLP.Gen13

open CFSG.KC.NortonSLPK CFSG.AGLEmbedding.Norton.Gen13

theorem parse_ok : parseEqB (decodeK (gen13Text0.toList ++ '\n' :: gen13Text1.toList)) S = true := by
  str_lits gen13Text0
  str_lits gen13Text1
  rw [String.toList_ofList, String.toList_ofList]
  quickRfl

end CFSG.KD.SLP.Gen13

end
