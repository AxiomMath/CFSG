module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def A314A5Excluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (C S L : Subgroup G),
    CFSG.SectionRank.IsSQTKCat ↥C → IsSylowTwoOf S C → pCoreOf 2 C ≠ ⊥ →
    pCoreOf 2 C ≤ Subgroup.centralizer (C : Set G) → L ≤ C → IsShort2 L → IsAltType L 5 →
    blockQ L = blockU L → blockZ L = ⊥ → S ≤ Subgroup.normalizer (L : Set G) → False

end CFSG.QuasithinUnique.A5
