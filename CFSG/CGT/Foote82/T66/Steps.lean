module

public import CFSG.CGT.Foote82.T66.Basic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

@[expose] def Climb66 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G S L R : Subgroup (GLV V))
    (r : GLV V), Extremal G S L → IsPGroup 2 R → R ≤ G →
      IsComponentOf L (G ⊓ Subgroup.centralizer (R : Set (GLV V))) → r ∈ R →
      r ∈ Subgroup.centralizer (R : Set (GLV V)) → orderOf r = 2 →
      IsComponentOf L (G ⊓ Subgroup.centralizer ({r} : Set (GLV V)))

@[expose] def CaseMC1 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G L : Subgroup (GLV V))
    (s : GLV V), StdForm G L s →
      CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1 → False

@[expose] def CaseMC2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G L : Subgroup (GLV V))
    (s : GLV V), StdForm G L s →
      2 ≤ CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) → False

end CFSG.CGT.Foote82
