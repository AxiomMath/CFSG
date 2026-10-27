module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Prog
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data
import CFSG.Certificates.Kernel.Common.StrLits

public section

set_option maxRecDepth 100000

namespace CFSG.KD.SLP.GenD13

open CFSG.KC.NortonSLPK CFSG.AGLEmbedding.Norton.GenD13

theorem parse_ok :
    parseEqB (decodeK (genD13Text0.toList ++ '\n' :: genD13Text1.toList)) S = true := by
  str_lits genD13Text0
  str_lits genD13Text1
  rw [String.toList_ofList, String.toList_ofList]
  quickRfl

end CFSG.KD.SLP.GenD13

end
