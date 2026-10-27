module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SporadicGammaPairs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporB7

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.AGLEmbedding

theorem sporadicTwoPairHolds_B_seven_of_oPrime
    (hB : SporadicBridges) (hBM : SporadicBMData)
    (hO : OPrimeCoreLeTwoAt 7 (NativeSporadic.Carrier .B)) : SporadicTwoPairHolds .B 7 := by
  refine sporadicTwoPairHolds_of_gamma hB Nat.prime_seven sporGammaOneAt_B_seven ?_ ?_ hO
  · intro S _ _ _ ⟨e⟩
    exact innerAut_eq_top_of_mulEquiv e
      (innerAut_eq_top_of_allInner CFSG.RankThree.PartOne.SPOR.allInner_B)
  · rw [hBM.1]
    norm_num

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
