module

public import CFSG.Quasithin.H13.L32AM50l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AM50j

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open Equiv Equiv.Perm
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem lemma14_7_50_mod_holds_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK)
    (h38 : Lemma14_7_38_F4) (h48 : Lemma14_7_48_F4) : Lemma14_7_50_Mod_F4 :=
  lemma14_7_50_mod_of_kIrr_F4 h1222 h1332 h1334 hA37 hA38 hA39 h38 h48 mod50KIrr

end CFSG.Quasithin.H13.L32A.C
