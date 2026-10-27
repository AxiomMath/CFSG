module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32K
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedW

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def K32TableW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    K32Ctx T M H S L s x z₁ z₂ K → IsListedComponentW M (sOne S x) K (z₁ * z₂) → KInEight K

end CFSG.QuasithinUnique.DoubleA3
