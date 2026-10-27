module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TwoPureA6U33
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TROne
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.AtlasOrders

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def U33FactsExact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsUThreeThree X →
    Subgroup.center X = ⊥ ∧ Open.pRank 3 (⊤ : Subgroup X) = 2

theorem u33Facts_of_exact (h : U33FactsExact) : U33Facts := fun X _ _ hX =>
  ⟨(h X hX).1, (h X hX).2.ge⟩

theorem smallRankAtlas_of_exact (h : U33FactsExact) : SmallRankAtlas := by
  intro X _ _ hX
  rcases hX with ⟨d, hd, ⟨e⟩⟩ | hU
  · have h168 : Nat.card X = 168 := OrdinaryProofs.l32Atlas_proved X ⟨d, hd, ⟨e⟩⟩
    have := pRank_top_le_one_of_card_168 h168
    omega
  · exact (h X hU).2.le

end CFSG.AGLEmbeddingD2.McLaughlin
