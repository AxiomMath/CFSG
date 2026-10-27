module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreePerm
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeCentral
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeSp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

theorem kFactTwelveNotLeSymThreeUnique_holds : KFactTwelveNotLeSymThreeUnique := by
  intro R _ _ h X W hX hW eX eW
  obtain ⟨eX⟩ := eX
  obtain ⟨eW⟩ := eW
  have hX' : X.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hX
  have hW' : W.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hW
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨n, ⟨e⟩⟩ | ⟨r, s, hs, ⟨e⟩⟩ | ⟨k, d, hk, ⟨q, hq, hd⟩, ⟨e⟩⟩ |
    ⟨f, hf, hker, hcard⟩
  · exact SymThree.eq_of_mulEquiv_perm_of_three_four_six hn e hX' eX eW
  · exact SymThree.eq_of_mulEquiv_perm e hX' eX eW
  · exact SymThree.eq_of_mulEquiv_perm_prod hs e hX' hW' eX eW
  · haveI := SymThree.isSimpleGroup_of_mulEquiv_lie_B hk hq hd e
    exact (SymThree.false_of_isSimpleGroup_of_isSubnormal hX' eX).elim
  · exact SymThree.eq_of_central_cover f hf hker hcard eX eW

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
