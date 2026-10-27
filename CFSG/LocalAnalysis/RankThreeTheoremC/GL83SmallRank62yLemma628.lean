module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yChoose
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yFitting
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yKFact
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem lemma628_of_interface (hS : Setting G) (hI : GL83SmallRankInterface G)
    (hK : KFactZAction628) : GL83SmallRankLemma628 G := by
  intro p P M x z T hf hcov
  obtain ⟨f, hfp, hf2, hfp', F₁, hF₁, hAF₁, hF₁M⟩ := sr628_exists_invariant hf hcov
  obtain ⟨h1, h3, h5⟩ := sr628_kfact_conclusion hS hI hK hf hfp hf2 hfp' hF₁ hAF₁ hF₁M
  exact ⟨h1, h3, h5, sr628_fitting_inf_eq_bot hI hf hcov h1 h3 h5⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
