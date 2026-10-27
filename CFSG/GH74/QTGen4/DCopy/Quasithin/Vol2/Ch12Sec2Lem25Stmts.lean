module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch12Sec2ChainStmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem12225Star_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p →
      T ⊓ Subgroup.centralizer (U : Set G) = U ⊔ (T ⊓ Subgroup.centralizer (I : Set G)) ∧
      U ⊓ Subgroup.centralizer (I : Set G) = ⊥ ∧
      T ⊓ Subgroup.centralizer (U : Set G) = U ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
      U ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      pCoreOf 2 (L ⊔ T) = V ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
      V ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      T ⊓ Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer (I : Set G) = ⊥ ∧
      IsElemAbelian 2 (T ⊓ Subgroup.centralizer (U : Set G)) ∧
      Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 ∧
      T = (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
      quasithinOmegaOneCenter T =
        (V ⊓ Subgroup.centralizer (T : Set G)) ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
      Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G)) = 2 ∧
      oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) ⊔ T ≤
        Subgroup.normalizer ((T ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G)

@[expose] def Lem12225YNormal_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p → n ≠ 3 →
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer
          ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) : Subgroup G) :
            Set G)

@[expose] def Lem12225CTL3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p → n = 3 →
      T ⊓ Subgroup.centralizer (L : Set G) = ⊥

@[expose] def Lem12225N5_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p → n = 3 ∨ n = 4

@[expose] def Lem12226Split_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p →
      ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L

end CFSG.Quasithin.H13
