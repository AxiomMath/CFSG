module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327bS331

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def CaseS2_1327_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
      Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))

@[expose] def O2H0One1327_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
    Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)) → pCoreOf 2 (S.H0 H) ≠ ⊥

@[expose] def Final1327_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
    Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)) → pCoreOf 2 (S.H0 H) ≠ ⊥ →
    ¬ ThreeTop (S.H0 H) → False

theorem rest1327_of_F4 (h13 : Lemma13213_F4) (hS2 : CaseS2_1327_F4) (hO2 : O2H0One1327_F4)
    (hfin : Final1327_F4) : Rest1327_F4 := by
  intro G _ _ T L V S H hH hHZ hsolv
  have hS3 := hS2 G T L V S H hH hHZ hsolv
  exact hfin G T L V S H hH hHZ hsolv hS3 (hO2 G T L V S H hH hHZ hsolv hS3)
    (h13 G T L V S H hH hHZ hsolv hS3)

theorem stmt13_2_7_of_parts_ofNoN_F4
    (h331 : Stmt3_3_1_F4) (h523 : Stmt5_2_3_F4) (h1222 : Stmt12_2_2_F4) (hE22 : E2.E22StatementNoN)
    (hRes : Res1328a_F4) (h13 : Lemma13213_F4) (hS2 : CaseS2_1327_F4) (hO2 : O2H0One1327_F4)
    (hfin : Final1327_F4) : Stmt13_2_7_F4 :=
  stmt13_2_7_ofNoN_F4 h331 h523 h1222 hE22 hRes (rest1327_of_F4 h13 hS2 hO2 hfin)

end CFSG.Quasithin.H13.A5
