module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.QuasithinUnique.L246.C123

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

@[expose] def ExcA7CentralZero : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsExcA7Block L → blockZ L = ⊥

end CFSG.QuasithinUnique.L246.C123
