module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K5192P2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNInputRed
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P2GlueAtM

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem k5192P2_of_factorShape (h : S15GNFactorShape) : K5192P2 :=
  k5192P2_of_atM fun X _ _ T hX hT _ T₁ T₂ hc =>
    ⟨(h X T hX hT T₁ T₂ hc).1.1, (h X T hX hT T₁ T₂ hc).2⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

end
