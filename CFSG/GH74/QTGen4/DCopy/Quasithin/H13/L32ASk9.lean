module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Input1476S2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ Y : Subgroup G, oTwoUpper Y = Y → Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) →
      (∀ y ∈ Y, y ^ 5 ∈ pCoreOf 2 Y) → Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y →
      H = Y ⊔ (L32A.l1 T L V ⊔ T) → H ≤ Subgroup.normalizer (L32A.l1 T L V : Set G) →
      (∀ N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), N.Normal → N ≠ ⊥ → N ≤ modO2Image H Y →
        N = modO2Image H Y) →
      (pCoreOf 2 Y).relIndex Y ≠ 25

end CFSG.Quasithin.H13
