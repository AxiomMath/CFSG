module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneReeF4
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneTrivialOn
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneSzSq
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialAlt
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicTits

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
  (SignalizerTrivialOn signalizerTrivialAlt_holds signalizerTrivialTits_holds)

theorem signalizerThreeAltTen_holds : SignalizerThreeAltTen := by
  intro h K _ _ hK
  obtain ⟨e⟩ := hK
  exact signalizerThreeOn_of_signalizerTrivialOn Nat.prime_five (by norm_num)
    (signalizerTrivialAlt_holds 5 Nat.prime_five le_rfl K ⟨e⟩)


theorem signalizerThreeLieFive_holds : SignalizerThreeLieFive := by
  intro d hd K _ _ hK
  rcases hd with hd | hd | hd
  · exact signalizerThreeOn_sz32 5 hd hK
  · obtain ⟨d, hv⟩ := d
    have hd' : d = .tits := hd
    subst hd'
    exact signalizerThreeOn_of_signalizerTrivialOn Nat.prime_five (by norm_num)
      (signalizerTrivialTits_holds K ⟨hv, hK⟩)
  · exact signalizerThreeOn_reeF4 hd hK

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
