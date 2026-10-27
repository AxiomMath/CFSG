module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrG2

public section

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabAutIrr CFSG.Assembly.LowTwoRank

namespace CFSG.HardMathSupport.Curtis.Coordinator

section G2


theorem outPTwoGen_of_lie {S : Type} [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : OutPTwoGen S p := by
  rcases classical_model_or_g2 d hd e with ⟨t, n, f, ht, h⟩ | ⟨q, hv, hq, rfl⟩
  · rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact outPTwoGen_psl h hp hp2
    · exact outPTwoGen_psu h
    · exact outPTwoGen_psp h hp
    · exact outPTwoGen_pomegaPlus h hp hp2
    · exact outPTwoGen_pomegaMinus h hp hp2
  · obtain ⟨K, _, _, _, f, hf, hK, ⟨e'⟩⟩ := exists_g2_field q hv hq e
    exact outPTwoGen_g2 e' hf hK hp

end G2

end CFSG.HardMathSupport.Curtis.Coordinator
