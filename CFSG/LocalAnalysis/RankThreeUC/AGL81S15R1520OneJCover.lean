module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneI
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneJ

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem pRank_pComponent_le_one {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {T T₁ T₂ : Subgroup X} (hcov : GNCoverSec T T₁ T₂) (h1 : mN T₁ p ≤ 1)
    (h2 : mN T₂ p ≤ 1)
    (hY : ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls → CFSG.Open.pRank p Ls ≤ 1)
    {I : Subgroup X} (hI : CFSG.IsPComponent p I) : CFSG.Open.pRank p I ≤ 1 :=
  pRank_pComponent_le_one_of_compositionFactor hp hp2 (fun S _ _ hcf hns => by
    rcases hcov S hcf hns with ⟨A, f, hA, hf⟩ | ⟨A, f, hA, hf⟩ | ⟨Ls, hLs, A, f, hA, hf⟩
    · exact pRank_le_one_of_section hp hp2 h1 hA f hf
    · exact pRank_le_one_of_section hp hp2 h2 hA f hf
    · exact pRank_le_one_of_section hp hp2 (hY Ls hLs) hA f hf) hI

end CFSG.LocalAnalysis.RankThreeUC.S15
