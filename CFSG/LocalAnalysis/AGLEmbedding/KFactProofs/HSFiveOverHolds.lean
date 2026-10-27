module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOverModel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOverU35
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOvergroups
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveU35

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.RankThree.Native

theorem hsU35Facts :
    HSU35Facts where
  card_UA := card_hsOUA
  UA_le_UA2 := hsOUA_le_UA2
  card_UA2 := card_hsOUA2
  card_R0 := card_hsOR0
  R0_le_UA := hsOR0_le_UA
  card_Z := card_commutator_hsOR0
  Z_le_centralizer := commutator_hsOR0_le_centralizer
  NU_le_UA := hsONU_le_UA
  UA_inf_normalizer := hsOUA_inf_normalizer
  orderOf_T := orderOf_hsOT
  T_commute := hsOT_commute_R0
  T_irreducible := hsOT_irreducible
  W_mem := hsOW_mem
  W_conj := hsOW_conj_mem
  closure_W := closure_insert_hsOW
  centralizer_T := hsOUA_inf_centralizer_T
  simple := hsOUA_isSimpleGroup
  E9 := hsOUA_E9

theorem kFactHSFiveOver_holds :
    KFactHSFiveOver := by
  have hA := overGood_hsOUA2_of hsU35Facts
  refine kFactHSFiveOver_of_model hsOR0_le_hs100P ?_ hs100R_normalizer_maximal
    hs100P_normalizer_overgroups hA (overGood_hsOUB2_of hA hsOW0_mem_normalizer hsOUB2_eq_map)
  rw [card_hsOR0]
  norm_num

end CFSG.AGLEmbeddingD2
