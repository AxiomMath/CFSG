module

public import CFSG.Quasithin.H13.NQS134Defs2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Producer134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Statements

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def StmtEnd134_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (z : G), NZ134 G T L V z → False

theorem stmt13_4_10_17_of_F4 (h1332 : Stmt13_3_2_F4) (hEnd : StmtEnd134_F4) : A6.Stmt13_4_10_17_F4 := by
  intro G _ _ T L V z h13 hirr hzv hz hzL hzM
  by_contra hns
  exact hEnd G T L V z
    { S := Classical.choice (A6.exists_setting134_F4 h1332 h13 hirr hzv)
      zV1 := hz
      zL := hzL
      zM := hzM
      nsolv := hns }

end CFSG.Quasithin.H13.NQS134
