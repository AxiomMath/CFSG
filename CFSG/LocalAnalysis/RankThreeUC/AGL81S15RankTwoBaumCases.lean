module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumA2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumB2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoG2Baum

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem K517_4b_baumPower_A2B2G2_of_cases (hA : K517_4b_baumPower_A2)
    (hB : K517_4b_baumPower_B2) (hG : K517_4b_baumPower_G2) : K517_4b_baumPower_A2B2G2 := by
  intro X _ _ T T₁ T₂ hX hGood Ls hY hinv d hd hRP hRT hLd q hq hq2 hqd s hs
  obtain ⟨Q, hQ | hQ | hQ⟩ := hd
  · exact hA X T T₁ T₂ hX hGood Ls hY hinv d ⟨Q, hQ⟩ hRP hRT hLd q hq hq2 hqd s hs
  · exact hB X T T₁ T₂ hX hGood Ls hY hinv d ⟨Q, hQ⟩ hRP hRT hLd q hq hq2 hqd s hs
  · exact hG X T T₁ T₂ hX hGood Ls hY hinv d ⟨Q, hQ⟩ hRP hRT hLd q hq hq2 hqd s hs

end CFSG.LocalAnalysis.RankThreeUC.S15

end
