module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdent
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieRows
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieSurv
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieG28
import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3ReeRank
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevTwoOuterGen
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ChevTwoSurvivorSchur
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitarySchur
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutElemRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeTheoremC KlingenIdentLieAux


theorem klingenIdentLie_holds : KlingenIdentLie := by
  intro p _ Y _ _ Rb Y₀ hred hcat hrank K hK huniq hnc hcent hkl d hd ⟨e⟩
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  rcases hd with ⟨n, hn⟩ | hU | hRee | hSp | hChev
  · exact (linTwo_false hred hrank hK hKn hcent hkl hn e).elim
  · exact (unitary_false kFactUnitarySchur kFactUnitarySylowStructure kFactUnitaryAutElemRank
      hred hrank hK hKn hcent hU e).elim
  · exact (ree_false kFactReeSchur kFactReeSylowElemAbelian hred hrank hK hRee e).elim
  · exact Or.inl hSp
  · rcases chevTwo_cases kFactChevTwoInnerRank_of_certificates kFactChevTwoOuterGen_of_certificates
      hred hrank hK hKn hcent hChev ⟨e⟩ with ⟨hp, h62⟩ | ⟨hp, h48⟩ | ⟨hp, hG⟩ | ⟨hp, hF⟩
    · exact Or.inr ⟨hp, h62⟩
    · exact (sp48_false kFactChevTwoSurvivorSchur hred hK hKn hcent hkl hp h48 e).elim
    · exact (g28_false kFactChevTwoSurvivorSchur hred hK hKn hcent hkl hp hG e).elim
    · exact (reeF4_false kFactChevTwoSurvivorSchur hred hK hKn hcent hkl hp hF e).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
