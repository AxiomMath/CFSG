module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.Main
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.Unitary
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.Ree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOutPPrime

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316

open CFSG.AGLEmbedding

section


theorem gl83I2316_of_smallIdent (hS : KFactSmallIdent) (hL : KFactOneLieIdent) : GL83I2316 :=
  gl83I2316_of_families ⟨hS, hL⟩ (kFactSmallOutPPrime_of_smallIdent hS)
    (fun p _ hp hp2 hd _ => planesGenerate_of_isUnitaryIndex hp hp2 hd)
    (fun p d hd => by
      have hp3 : p = 3 := hd.1
      subst hp3
      exact planesGenerate_of_isReeGTwoIndex hd)

theorem gl83I2316_of_gl83I241 (h : GL83I241) : GL83I2316 :=
  gl83I2316_of_smallIdent h.1 h.2

end

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316
