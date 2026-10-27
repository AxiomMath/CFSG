module

public import CFSG.Quasithin.H13.A6S1519
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1513

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem lemma13_5_19_two_L1_F4
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4)
    (hcon : ∀ H' ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H') →
      ¬ H' ≤ Subgroup.normalizer (S.L1 : Set G))
    {H : Subgroup G} (hH : H ∈ S.Hz) :
    V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (S.L1 : Set G)) := by
  by_contra hV
  have hVH1 : V ≤ H ⊓ Subgroup.normalizer (S.L1 : Set G) :=
    le_inf (S.hypF91_F4 hNS h13315 h1356two hH).V_le_H (S.V_le_T.trans S.T_le_normalizer_L1)

  have hM : ¬ H ⊓ Subgroup.normalizer (S.L1 : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun h => hV (S.V_le_pCoreOf_of_le_M hVH1 h)
  have hH1 := S.normalizer_L1_mem_Hz hH hM
  have hF1 := S.hypF91_F4 hNS h13315 h1356two hH1

  have hna : ¬ IsElemAbelian 2 (conjClosure S.V3 (H ⊓ Subgroup.normalizer (S.L1 : Set G))) := by
    intro hab
    refine hV (hF1.F94_2 ((Subgroup.commutator_mono le_rfl inf_le_left).trans
      (S.comm_centralizer_V3_F4 h13315 _)) fun x hx y hy => ?_)
    exact congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact hcon _ hH1 hna inf_le_right

end Setting4

end CFSG.Quasithin.H13.A6
