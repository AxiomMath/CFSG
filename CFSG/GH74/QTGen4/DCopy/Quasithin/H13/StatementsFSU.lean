module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Stmt13_3_2_two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), QTH13 G T L →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      T ≤ Subgroup.normalizer (K : Set G) ∧ quasithinIsMaximalLocal T K ∧
        quasithinIsMaxTwoLocal (Subgroup.normalizer (K : Set G)) ∧
        ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → K ⊔ T ≤ M →
          M = Subgroup.normalizer (K : Set G)

@[expose] def Stmt13_3_2_three_fsu_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), QTH13 G T L →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      (∃ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V) ∧
        ∀ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V →
          V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧ FSU G T K V

@[expose] def Stmt14_4_14_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14_3_1One G T L → FSU G T L V →
    ¬ IsMulCommutative ↥(fsuU T V) →
      Nonempty (G ≃* NativeSporadic.HS) ∨ LieModel G .G2 0 3 1

@[expose] def Stmt14_7_75_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14_3_1One G T L → FSU G T L V →
    IsMulCommutative ↥(fsuU T V) → Nonempty (G ≃* NativeSporadic.Ru)

end CFSG.Quasithin.H13
