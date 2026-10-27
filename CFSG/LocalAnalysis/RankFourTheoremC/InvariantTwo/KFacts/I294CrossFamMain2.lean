module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamMain
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamULarge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

theorem crossFamUnitaryGeThree_of_large (h : CrossFamUnitaryLarge) : CrossFamUnitaryGeThree :=
  fun m hm q hv => crossAt_unitary_of_large (h m hm q hv)

section Reduced


theorem kd29Cross_reduced_of_large (htA : CrossFamUnitaryLarge) (hB : CrossFamB)
    (hC : CrossFamC) (hD : CrossFamD) (htD : CrossFamTwistedD) (hE6 : CrossFamE6)
    (htE6 : CrossFamTwistedE6) (hE7 : CrossFamE7) (hE8 : CrossFamE8) (hF4 : CrossSylowAbelianF4)
    (hG2 : CrossSylowAbelianG2) (htr : CrossSylowAbelianTrialityD4)
    (hRG : CrossSylowAbelianReeG2) (hRF : CrossSylowAbelianReeF4) : KD29Cross :=
  kd29Cross_reduced_of_linear (crossFamUnitaryGeThree_of_large htA) hB hC hD htD hE6 htE6 hE7 hE8
    hF4 hG2 htr hRG hRF

end Reduced

end CFSG.LocalAnalysis.RankFourTheoremC
