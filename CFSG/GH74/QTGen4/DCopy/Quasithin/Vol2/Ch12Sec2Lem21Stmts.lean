module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem21Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Lem12220PickFull_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → IsHStar T (Subgroup.normalizer (L : Set G)) H → Group.IsSolvable ↥H →
      ∃ (P U I : Subgroup G) (h : G) (p : ℕ), Pre12_2_21 T L V H P U I h p

@[expose] def Lem12221_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h p → U ≤ pCoreOf 2 H

@[expose] def Lem12222_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h p → U ≤ pCoreOf 2 H →
      ∃ (P' U' I' W : Subgroup G) (h' v : G), Pre12_2_21 T L V H P' U' I' h' p ∧
        U' ≤ pCoreOf 2 H ∧ Data12_2_22 V H P' U' W v p

@[expose] def Lem12223_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I W : Subgroup G) (h v : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h p → U ≤ pCoreOf 2 H → Data12_2_22 V H P U W v p →
      Nat.card P = p

@[expose] def Lem12223Post_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I W : Subgroup G) (h v : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h p → U ≤ pCoreOf 2 H → Data12_2_22 V H P U W v p →
    Nat.card P = p →
      U = W ∧ H ≤ Subgroup.normalizer (U : Set G) ∧ H ≤ Subgroup.normalizer (I : Set G) ∧
        I = P ⊔ U ⊔ V ∧ H = I ⊔ T ∧ U ⊓ Subgroup.centralizer (P : Set G) = ⊥ ∧
        ⁅pCoreOf 2 (L ⊔ T), U⁆ ≤ U ⊓ V

end CFSG.Quasithin.H13
