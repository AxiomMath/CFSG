module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.FixedPoint

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type*} [Group G] {Γ W : Type*} [Group Γ] [AddCommGroup W] [MulAction Γ W]

@[expose] def ThreeFixedModel (Γ W : Type*) [Group Γ] [MulAction Γ W] : Prop :=
  ∀ w : W, ∃ g : Γ, orderOf g = 3 ∧ g • w = w

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
