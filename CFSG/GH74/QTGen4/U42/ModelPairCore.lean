module

public import CFSG.GH74.QTGen4.U42.PairExt
public import CFSG.GH74.QTGen4.U42.ModelP1CharTwo

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.F431.U42 U42F431

theorem model_pairCore : PairCore P1 B0 T (pCoreOf 2 P1) := by
  have hSyl : IsSylowTwoOf T P1 := by
    refine ⟨T_le_B0.trans B0_le_P1, isSylow_T.2.1, ?_⟩
    show ¬ 2 ∣ T.relIndex P1
    have h := Subgroup.relIndex_mul_card (H := T) (K := P1)
    rw [inf_eq_left.mpr (T_le_B0.trans B0_le_P1), card_T, card_P1] at h
    have : T.relIndex P1 = 9 := by omega
    rw [this]
    norm_num
  refine ⟨F7.isSylowTwoOf_pCoreOf_le hSyl, T_le_B0, B0_le_P1, ?_,
    hSyl.2.1, hSyl.2.2, centralizer_pCoreOf_P1_le, ?_⟩
  · intro h hh u hu
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P1 hh) u).mp hu
  · rw [card_P1, card_T]

end CFSG.GH74.QTGen4.U42
