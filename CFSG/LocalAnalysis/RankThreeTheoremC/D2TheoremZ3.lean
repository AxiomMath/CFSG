module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem d2TheoremZ3_of (hX : D1NoXBlock3 G) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) : D2TheoremZ3 G := by
  intro hS hD1 M hM ha hb p hp P A H hMP hesc hmax hsurv hO
  have : Fact p.Prime := ⟨hesc.prime⟩
  have hglob := aglGlobal_of_setting hS
  refine false_of_survivorsAt hglob (d1At_of_theoremD1 hD1 hp) h84 hCGT
    (noXBlockFor_of_setting hX hS) hesc hmax (fun H' h' => ?_) hO
  obtain ⟨hD, hC⟩ := hsurv H' h'
  exact h'.survivorData_of_reduced hglob hD hC

end CFSG.LocalAnalysis.RankThreeTheoremC
