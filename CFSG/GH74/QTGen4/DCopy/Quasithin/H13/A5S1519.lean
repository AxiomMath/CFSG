module

public import CFSG.Quasithin.H13.A5S1519
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S135

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open scoped Pointwise

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem lemma_13_5_19_two_F4 (h1323 : Input1323Two_F4)
    (hcon : ∀ H' ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H') →
      ¬ H' ≤ Subgroup.normalizer (S.L1 : Set G))
    {H : Subgroup G} (hH : H ∈ S.Hz) :
    V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (S.L1 : Set G)) := by
  by_contra hV
  have hVH1 : V ≤ H ⊓ Subgroup.normalizer (S.L1 : Set G) :=
    le_inf ((S.hypF91_F4 h1323 hH).V_le_H)
      (S.V_le_T.trans S.T_le_normalizer_L1)

  have hM : ¬ H ⊓ Subgroup.normalizer (S.L1 : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun h => hV (S.V_le_pCoreOf_of_le_M hVH1 h)
  have hH1 := S.normalizer_L1_mem_Hz hH hM

  have hna : ¬ IsElemAbelian 2 (conjClosure S.V3 (H ⊓ Subgroup.normalizer (S.L1 : Set G))) :=
    fun hab => hV (((S.tfae_13_5_10_F4 h1323 hH1).out 1 2).2 hab)
  exact hcon _ hH1 hna inf_le_right

end Setting

end CFSG.Quasithin.H13.A5
