module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTwoGroupCases
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizerBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizerInner
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizerFamilies
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34TwoSig
import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer

open CFSG.LocalAnalysis.RankFourTheoremC

section Assembly


theorem twoSignalizerFive_holds : TwoSignalizerFive := by
  intro X _ _ K hKn hs hnab B hB hBc hBC hcase T hT hBT
  haveI : K.Normal := hKn
  obtain ⟨hcase, hBK⟩ := hcase
  rcases hcase with ⟨hv, e⟩ | e | e
  · exact commutator_le_centralizer_of_signalizerAutAt (by norm_num) (by norm_num)
      (signalizerAutAt_tits rfl rfl) e hB hBc hBC (Or.inl hBK) hT hBT
  · exact commutator_le_centralizer_of_signalizerAutAt (by norm_num) (by norm_num)
      (signalizerAutAt_mcl rfl) e hB hBc hBC (Or.inl hBK) hT hBT
  · exact twoSignalizerFi22_holds X K hKn hs hnab B hB hBc hBC ⟨e, hBK⟩ T hT hBT

theorem signalizerTwoGroupKFact_of_l28 (hL28 : TwoSignalizerL28) : SignalizerTwoGroupKFact :=
  signalizerTwoGroupKFact_of_cases twoSignalizerL2_holds twoSignalizerU3_holds
    twoSignalizerAlt_holds twoSignalizerL34 twoSignalizerM11_holds twoSignalizerFive_holds
    twoSignalizerJ4_holds hL28 twoSignalizerSz32_holds

theorem twoSignalizerL28_holds : TwoSignalizerL28 :=
  twoSignalizerL28_of fun _ hd => signalizerAutAt_of_gl83 gl83SignalizerAut_holds Nat.prime_three
    (by norm_num) (GL83Type24.linTwoEight rfl hd)

theorem signalizerTwoGroupKFact_holds : SignalizerTwoGroupKFact :=
  signalizerTwoGroupKFact_of_l28 twoSignalizerL28_holds

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer
