module

public import CFSG.Quasithin.H13.A5X1367n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem GvS_le_normalizer_conjClosure_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) :
    autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer ((conjClosure (autOn K S.Uv) (autOn S.Tv S.Uv) :
        Subgroup (MulAut ↥S.Uv)) : Set (MulAut ↥S.Uv)) := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have hN := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38
    (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF) (S.isSylowTwoOf_Tv_F4 h1222 h517) hK
  rw [← autOn_conjClosure ((le_of_mem_cComp hK).trans S.Gv_le_normalizer_Uv)
    (S.Tv_le_Gv.trans S.Gv_le_normalizer_Uv)]
  exact autOn_le_normalizer_autOn hN

theorem inYz_of_goodComp_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hgood : S.GoodComp (autOn K S.Uv)) : S.InYz K := by
  refine ⟨le_of_mem_cComp hK, cComp_subset_lFamily S.Tv_le_Gv hK, ?_,
    S.inXz_of_goodComp hgood (S.GvS_le_normalizer_conjClosure_F4 h1222 h517 h37 h38 hF hK)⟩
  have hq : CFSG.IsQuasisimple ↥(autOn K S.Uv) := B1Red.isQuasisimple_of_open hgood.1.2.2
  have hO : CFSG.pCore 2 ↥(autOn K S.Uv) = ⊥ := by
    have h1 : pCoreOf 2 (autOn K S.Uv) = ⊥ :=
      le_bot_iff.mp ((pCoreOf_two_le_of_subnormal hgood.1.2.1).trans
        (S.pCoreOf_GvS_F4 h1222 h517 hF).le)
    rw [CFSG.pCore_eq_open]
    exact (Subgroup.map_eq_bot_iff_of_injective _ (autOn K S.Uv).subtype_injective).mp h1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm)) hq

end Setting

end CFSG.Quasithin.H13.A5
