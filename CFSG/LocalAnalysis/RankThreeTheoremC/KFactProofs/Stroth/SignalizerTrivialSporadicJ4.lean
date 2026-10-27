module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicD2
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigJ4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.LocalAnalysis.RankFourTheoremC
  CFSG.AGLEmbeddingD2.Wilson.Coordinator


theorem signalizerTrivialJ4_holds : SignalizerTrivialJ4 := by
  intro K _ _ hK
  obtain ⟨e⟩ := hK
  have eKJ : K ≃* J :=
    e.trans ((CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv.some).symm.trans
      (seedEquiv j4Facts.mat))
  exact signalizerTrivialOn_of_d2Heis (by norm_num) d2HeisLocalAt_J4 (signalizerAutAt_jFour rfl)
    ⟨e⟩ (@center_eq_bot_of_mulEquiv K _ J (Subgroup.toGroup J) eKJ center_J)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
