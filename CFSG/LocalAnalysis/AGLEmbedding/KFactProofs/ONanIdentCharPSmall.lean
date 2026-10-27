module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentCharPBasic
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLieCharRankProof
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinTwo

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Certificates


theorem smallIdentLieCharP : SmallIdentLieCharP := by
  intro K _ _ _ _ d he p hpc hp hp2 T hT hΓ hr
  obtain ⟨e⟩ := he
  by_cases hsmall : CFSG.AGLEmbeddingD2.IsD2LieCharSmall p d.1
  · obtain ⟨q, hqp, hq⟩ := hsmall
    rcases hq with ⟨hq2, hd⟩ | ⟨hq1, hd | hd⟩
    · rcases (show q.exponent = 1 ∨ q.exponent = 2 by have := q.exponent_pos; omega) with h1 | h2
      · exact absurd (isCyclic_sylow_of_pRank_le_one hp hp2
          (CFSG.AGLEmbeddingD2.kFactLinTwoPrimeRank K d ⟨e⟩ p hp hp2 ⟨q, hqp, h1, hd⟩) T) hT
      · exact Or.inl ⟨d, ⟨q, hd, hqp, h2⟩, ⟨e⟩⟩
    · refine absurd (top_le_iff.mp ?_) hΓ
      rw [← CFSG.AGLEmbeddingD2.kFactLinThreeCore K d ⟨e⟩ p hp hp2 ⟨q, hqp, hq1, hd⟩ T]
      exact CFSG.AGLEmbeddingD2.glbCore_anti p (by norm_num) _
    · exact Or.inr (Or.inl ⟨d, ⟨q, hqp, hq1, hd⟩, ⟨e⟩⟩)
  · have := CFSG.AGLEmbeddingD2.kFactLieCharRank K d ⟨e⟩ p hp hp2 hpc hsmall
    omega

end Certificates

end CFSG.AGLEmbedding
