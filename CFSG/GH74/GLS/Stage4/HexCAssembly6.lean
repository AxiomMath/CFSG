module

public import CFSG.GH74.GLS.Stage4.RestZFH3
public import CFSG.GH74.GLS.Stage4.HexCAssembly2

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.RankTwo CFSG.GH74.GLS.Stage4.Rest
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

theorem s_ch6_Std_of_rest_leaves6
    (hT2 : Ch6RestT2SH) (hG9 : Ch6T2Good9XH) (hB9 : Ch6T2Bad9)
    (hGGt9 : Ch6T2GoodGt9XH) (hBGt9 : Ch6T2BadGt9)
    (hN : Ch6NondegLeaf2) (hZ : Ch6ZFusionAll) : S_ch6_Std :=
  s_ch6_Std_of_matchtN2
    (ch6LocalRGD2tN2_of_plusN2 fun G _ _ hStd hr Gs _ hG2 => by
      obtain ⟨q₁, q₂, hAt⟩ := (isTwoCentralG2TypeG2_iff_exists_at G Gs).1 hG2
      exact hN G hStd hr Gs q₁ q₂ hAt
        (ch6OutPlus_of_H hT2 hG9 hB9 hGGt9 hBGt9 hZ hStd hr hG2))

end CFSG.GH74.GLS.Stage4.Hex
