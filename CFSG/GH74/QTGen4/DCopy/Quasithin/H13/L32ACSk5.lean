module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_36_HatIrr_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (L32A.l1 T L V ⊔ T) →
      IsHat (L32A.cStar K) (CFSG.Blueprint.NativeSporadic.Carrier .M22) →
      ∀ J : Subgroup G, fsuV1 T V ≤ J → J ≤ conjClosure V H →
        K ≤ Subgroup.normalizer (J : Set G) → J = fsuV1 T V ∨ J = conjClosure V H

end CFSG.Quasithin.H13.L32A.C
