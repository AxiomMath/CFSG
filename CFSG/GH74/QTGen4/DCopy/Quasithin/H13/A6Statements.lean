module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A6Statements

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Stmt13_4_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → LieModel G .PSp 3 2 1

@[expose] def Stmt13_4_9_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (z : G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → z ∈ fsuV1 T V →
    z ∉ Subgroup.centralizer (L : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) →
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) → LieModel G .PSp 3 2 1

@[expose] def Stmt13_4_10_17_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (z : G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → z ∈ fsuV1 T V →
    z ∉ Subgroup.centralizer (L : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) →
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G))

@[expose] def Stmt13_5_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), QTH13 G T L → ¬ LieModel G .PSp 3 2 1 →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
        LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨
        (Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) ∧
          Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3 ∧
          Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
            alternatingGroup (Fin 6)))) ∧
      (T ≤ Subgroup.normalizer (K : Set G) ∧ quasithinIsMaximalLocal T K) ∧
      (∃ VK : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T VK) ∧
      ∀ VK : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T VK →
        VK ≤ reducedAggregate (K ⊔ T) ∧ VK ≤ T ∧ T ≤ Subgroup.normalizer (VK : Set G) ∧
        FSU G T K VK ∧ VK ⊓ Subgroup.centralizer (K : Set G) = ⊥ ∧
        ∃ _ : IsMulCommutative ↥VK,
          AlternatingNatural (V := ↥VK) (autOn K VK) ⊤ ⊥ 5 ∨
            AlternatingNatural (V := ↥VK) (autOn K VK) ⊤ ⊥ 6 ∨
            BinaryNaturalSL (V := ↥VK) (autOn K VK) ⊤ ⊥ 3 1

@[expose] def Stmt13_5_12_six_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → ¬ LieModel G .PSp 3 2 1 →
    ¬ IsMulCommutative ↥(conjClosure (v3 T L V) (g1 T V)) → LieModel G .PSU 4 3 1

@[expose] def Stmt13_7_8_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → ¬ LieModel G .PSp 3 2 1 →
    ¬ LieModel G .PSU 4 3 1 → IsMulCommutative ↥(conjClosure V (g1 T V))

end CFSG.Quasithin.H13.A6
