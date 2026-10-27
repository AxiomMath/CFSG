module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2f
public import CFSG.Quasithin.Background.HOm4Aut
public import CFSG.Quasithin.H13.L32AL2g

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable {X : TopCtx T L V K W t₀} [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

theorem relIndex_img_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {R S : Subgroup G} (hRS : R ≤ S)
    (hS : S ≤ A6.g1 T V) (hQR : pCoreOf 2 (A6.g1 T V) ≤ R) :
    (X.img R).relIndex (X.img S) = R.relIndex S := by
  have hker : X.top.act.ker = (pCoreOf 2 (A6.g1 T V)).subgroupOf (A6.g1 T V) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      X.act_eq_one_iff_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334]
  rw [img, img, Subgroup.relIndex_map_map, hker,
    sup_eq_left.mpr (Subgroup.subgroupOf_mono _ hQR),
    sup_eq_left.mpr (Subgroup.subgroupOf_mono _ (hQR.trans hRS)), Subgroup.relIndex_subgroupOf hS]

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
