module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicD2
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigTits
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

open CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.RankFourTheoremC CFSG.AGLEmbeddingD2


theorem signalizerTrivialTits_holds : SignalizerTrivialTits := by
  intro K _ _ hiso
  obtain ⟨hv, ⟨e⟩⟩ := hiso
  obtain ⟨eS⟩ := titsModelEquiv K 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  have hd : (⟨.tits, hv⟩ : TauCeti.ValidLieTypeIndex).1 = .tits := rfl
  exact signalizerTrivialOn_of_d2Torus Nat.prime_five (d2TorusLocalAt_tits _ hd)
    (signalizerAutAt_tits rfl hd) ⟨e⟩ (center_eq_bot_of_mulEquiv eS titsD_center)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
