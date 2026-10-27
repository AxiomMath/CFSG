module

public import CFSG.ClassicalInvolution.Q3.Q3ZASym
public import CFSG.ClassicalInvolution.Q3.Q3ZAStmt

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z


theorem c3ChainInput_of_pieces (hT : TriangleExists) (hH : HeisAtTheorem) : C3ChainInput := by
  intro G _ _ _ hnab K z hR hshape hO3
  have hctx : Ctx G K z := ⟨hnab, hR, hshape, hO3⟩
  obtain ⟨T⟩ := hT G K z hctx
  have hA2 := T.steinbergA2_of_heisAt (hH G K z hctx T.Θ₀₁ T.Θ₁₂ T.Θ₀₂ T.layerTriple)
  obtain ⟨T₀, h₀, T₁, h₁, hW⟩ := exists_a2_of_steinbergA2 hA2
  exact chain_of_frame T.toFrame h₀ h₁ hW

end CFSG.ClassicalInvolution.Q3.Q3ZA
