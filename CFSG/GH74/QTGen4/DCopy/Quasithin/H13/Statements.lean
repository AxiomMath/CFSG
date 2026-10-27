module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups

@[expose] def Stmt13_1_7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def Stmt13_1_2_three_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → QT13Five (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def Stmt13_3_16_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), QTH13 G T L →
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1

@[expose] def Stmt13_6_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), QTH13 G T L →
    quasithinO2QuotientIso L (alternatingGroup (Fin 5)) →
      LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1

@[expose] def Stmt13_8_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), QTH13 G T L →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 6)) →
      LieModel G .PSp 3 2 1 ∨ LieModel G .PSU 4 3 1

@[expose] def Stmt14_8_1_three_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), QTH13 G T L →
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
      LieModel G .PSp 3 2 1 ∨ LieModel G .G2 0 3 1 ∨
        Nonempty (G ≃* NativeSporadic.HS) ∨ Nonempty (G ≃* NativeSporadic.Ru)

end CFSG.Quasithin.H13
