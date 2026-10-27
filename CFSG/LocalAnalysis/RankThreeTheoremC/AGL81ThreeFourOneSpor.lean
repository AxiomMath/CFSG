module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneSporFive
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneSporSeven
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneTrivialOn
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicMcL
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicJ4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

theorem signalizerThreeAt_mcl :
    SignalizerThreeAt 5 (TauCeti.CFSGIndex.sporadic .McL).Group := by
  intro K _ _ hK
  exact signalizerThreeOn_of_signalizerTrivialOn Nat.prime_five (by norm_num)
    (signalizerTrivialMcL_holds K hK)

theorem signalizerThreeAt_j4 :
    SignalizerThreeAt 11 (TauCeti.CFSGIndex.sporadic .J4).Group := by
  intro K _ _ hK
  exact signalizerThreeOn_of_signalizerTrivialOn (by norm_num) (by norm_num)
    (signalizerTrivialJ4_holds K hK)

theorem signalizerThreeSporadic_holds :
    SignalizerThreeSporadic := by
  unfold SignalizerThreeSporadic
  refine ⟨?_, ?_, signalizerThreeAt_j4⟩
  · rintro s (rfl | rfl | rfl)
    exacts [signalizerThreeAt_mcl, signalizerThreeAt_hs, signalizerThreeAt_ru]
  · rintro s (rfl | rfl | rfl)
    exacts [signalizerThreeAt_onan, signalizerThreeAt_fi24Prime, signalizerThreeAt_he]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
