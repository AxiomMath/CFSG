module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuterReduction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLieCharRankProof
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeOut
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRankAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.SeitzGeneration
  CFSG.AGLEmbeddingD2

section Char


theorem charPCyclicSylow_holds : CharPCyclicSylow := by
  intro K _ _ d ⟨e⟩ p hp hp2 hpc T hT
  by_cases hsmall : IsD2LieCharSmall p d.1
  · exact kFactLieCharOut K d ⟨e⟩ p hp hp2 hsmall
  · exfalso
    have h3 := kFactLieCharRank K d ⟨e⟩ p hp hp2 hpc hsmall
    haveI : Fact p.Prime := ⟨hp⟩
    have hrk : RankLE1 p K := fun A hA =>
      CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow T hT hA
    exact false_of_two_le_pRank hp hrk (le_trans (by norm_num) h3)

end Char

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter
