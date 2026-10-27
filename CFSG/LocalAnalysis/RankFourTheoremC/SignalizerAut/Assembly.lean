module

public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.LinTwo
public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Unitary
public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Alt
public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Ree
public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.LinTwoEight
public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.MEleven
public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.LinThreeFour
public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.FiTwentyTwo
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigJ4
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigMcL
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigSz
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigTits

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

theorem gl83SignalizerAut_of_types
    (h : ∀ (p : ℕ) (i : TauCeti.CFSGIndex), p.Prime → p ≠ 2 → GL83Type24 p i →
      SignalizerAutAt p i) : GL83SignalizerAut :=
  fun K _ _ p i hp hp2 hi e B Y hB hBc hY hBY hin => h p i hp hp2 hi K e B Y hB hBc hY hBY hin

theorem gl83SignalizerAut_holds
    : GL83SignalizerAut := by
  refine gl83SignalizerAut_of_types fun p i hp hp2 hi => ?_
  cases hi with
  | linTwo hn hd => exact signalizerAutAt_linTwo hp hp2 hn hd
  | unitary hd => exact signalizerAutAt_unitary hp hd
  | altTwoP h => exact signalizerAutAt_altTwoP hp hp2 h
  | ree hd => exact signalizerAutAt_ree hd
  | linTwoEight hp3 hd => exact signalizerAutAt_linTwoEight hp3 hd
  | mEleven hp3 => exact signalizerAutAt_mEleven hp3
  | linThreeFour hp3 hd => exact signalizerAutAt_linThreeFour hp3 hd
  | suzuki hp5 hd => exact signalizerAutAt_suzuki hp5 hd
  | tits hp5 hd => exact signalizerAutAt_tits hp5 hd
  | mcl hp5 => exact signalizerAutAt_mcl hp5
  | fiTwentyTwo hp5 => exact signalizerAutAt_fiTwentyTwo hp5
  | jFour hp11 => exact signalizerAutAt_jFour hp11

end CFSG.LocalAnalysis.RankFourTheoremC
