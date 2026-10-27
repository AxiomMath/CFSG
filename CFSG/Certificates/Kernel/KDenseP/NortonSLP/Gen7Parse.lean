module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7Prog
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.Gen7.Data
import CFSG.Certificates.Kernel.Common.StrLits

public section

set_option maxRecDepth 100000

namespace CFSG.KD.SLP.Gen7

open CFSG.KC.NortonSLPK CFSG.AGLEmbedding.Norton.MON5_7.Gen7

theorem parse_ok : parseEqB (decodeK (gen7Text0.toList ++ '\n' :: gen7Text1.toList)) S = true := by
  str_lits gen7Text0
  str_lits gen7Text1
  rw [String.toList_ofList, String.toList_ofList]
  quickRfl

end CFSG.KD.SLP.Gen7

end
