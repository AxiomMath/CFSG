module

public import CFSG.Quasithin.H13.GoldschmidtL1329Five
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Producer134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L139

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

@[expose] def Stmt13_2_2_9L1Perm_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → IsHatA6 L →
      V ⊓ centralizer (L : Set G) ≠ ⊥ →
        normalizer (L₁Of L (fsuV1 T V) : Set G) ≤ normalizer (L : Set G)

@[expose] def Stmt13_2_2_9L1Nat_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → IsHatA6 L →
      V ⊓ centralizer (L : Set G) = ⊥ →
        normalizer (L₁Of L (fsuV1 T V) : Set G) ≤ normalizer (L : Set G)

theorem stmt13_2_2_9L1_of_cases_F4 (hN : Stmt13_2_2_9L1Nat_F4) (hP : Stmt13_2_2_9L1Perm_F4) :
    Stmt13_2_2_9L1_F4 := by
  intro G _ _ T L V hH hV hA6 hhat
  by_cases hZV : V ⊓ centralizer (L : Set G) = ⊥
  · exact hN G T L V hH hV hA6 hhat hZV
  · exact hP G T L V hH hV hA6 hhat hZV

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stmt13_2_2_9L1Perm_holds_F4 (h1332 : Stmt13_3_2_F4) :
    Stmt13_2_2_9L1Perm_F4 := by
  intro G _ _ T L V hH hV _ hhat hZV
  obtain ⟨S⟩ := exists_setting134_F4 h1332 hH hV hZV
  exact stmt13_2_2_9L1_of_setting134 S hhat

end CFSG.Quasithin.H13.U3
