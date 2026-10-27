module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.L32ANotation

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_5_5Q_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ Y : Subgroup G), Hyp147 G T L V →
    A6.IsV2 T V V₂ → oTwoUpper Y = Y → Y ≤ A6.g1 T V → T ≤ Subgroup.normalizer (Y : Set G) →
    quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3)) →
    ¬ Y ≤ Subgroup.normalizer (L : Set G) →
    quasithinO2QuotientIso (L₁Of L V₂ ⊔ T) (Equiv.Perm (Fin 3)) →
    (L₁Of L V₂ ⊔ T) ⊓ (Y ⊔ T) = T →
    pCoreOf 2 (L₁Of L V₂ ⊔ Y ⊔ T) ≠ ⊥

end CFSG.Quasithin.H13
