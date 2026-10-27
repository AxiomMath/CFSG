module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.L32ASk5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_8_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ¬ (IsCyclic ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) ∧
      IsPGroup 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))))

@[expose] def Lemma14_7_9_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ (Y : Subgroup G) (p : ℕ), p.Prime → oTwoUpper Y = Y → Y ≤ H →
      H ≤ Subgroup.normalizer (Y : Set G) → (∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y) →
      pCoreOf 2 Y < Y ⊓ Subgroup.normalizer (L : Set G) →
      p = 3 ∧
        (Y = L32A.l1 T L V ∨
          (IsPOnePlusTwo 3 (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y) ∧
            L32A.l1 T L V ⊔ pCoreOf 2 Y = L32A.o2z Y ∧
            L32A.l1 T L V = oTwoUpper (L32A.o2z Y) ∧
            (∀ W : Subgroup G, L32A.l1 T L V ⊔ pCoreOf 2 Y ≤ W → W ≤ Y →
              T ≤ Subgroup.normalizer (W : Set G) →
              W = L32A.l1 T L V ⊔ pCoreOf 2 Y ∨ W = Y) ∧
            L32A.l1 T L V = oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G))))

end CFSG.Quasithin.H13
