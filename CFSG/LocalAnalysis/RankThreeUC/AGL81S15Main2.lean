module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OModuleFacts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem agl81TheoremDSection15_of_ctx2
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (hGN : S15GNInput)
    (hF : ∀ (G : Type) [Group G] [Finite G], Standing G →
      ∀ (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M), S15Ctx2 G M T T₁ T₂ → False) :
    CFSG.Yardstones.M9cbf837c48cf.AGL81TheoremDSection15Statement := by
  intro G _ _ _ hnab hK hC hrank
  have hS : Standing G := ⟨inferInstance, hnab, hK, hC, hrank⟩
  exact agl81Residual7NoU4_of_ctx2 hS (d1NoXBlock3_of_inputsK h1 h2 h25) hGN
    (CFSG.Yardstones.M9cbf837c48cf.agl81TheoremDSection16_proved G hnab hK hC hrank) (hF G hS)

end CFSG.LocalAnalysis.RankThreeUC.S15
