module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtRows0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtRows1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtRows2

public section

set_option maxRecDepth 100000

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open PkG Chain

@[expose] def rowsT : List (List ℕ) :=
  rowsT0 ++
  rowsT1 ++
  rowsT2 ++
  rowsT3 ++
  rowsT4 ++
  rowsT5 ++
  rowsT6 ++
  rowsT7 ++
  rowsT8 ++
  rowsT9 ++
  rowsT10 ++
  rowsT11

theorem rowsT_chk : chainChk rowVal rowOk 0 rowsT = true := by
  have h11 := (chainTo_iff _ _ _ _ _ rowsT11_chk).1
  have h10 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT10_chk h11
  have h9 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT9_chk h10
  have h8 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT8_chk h9
  have h7 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT7_chk h8
  have h6 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT6_chk h7
  have h5 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT5_chk h6
  have h4 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT4_chk h5
  have h3 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT3_chk h4
  have h2 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT2_chk h3
  have h1 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT1_chk h2
  have h0 := chainChk_chunk rowVal rowOk _ _ _ _ rowsT0_chk h1
  exact h0

theorem cntC2_append (a b : List (List ℕ)) : cntC2 (a ++ b) = cntC2 a + cntC2 b := by
  simp [cntC2, List.filter_append]

theorem cntC4_append (a b : List (List ℕ)) : cntC4 (a ++ b) = cntC4 a + cntC4 b := by
  simp [cntC4, List.filter_append]

theorem cnt1_append (a b : List (List ℕ)) : cnt1 (a ++ b) = cnt1 a + cnt1 b := by
  simp [cnt1, List.filter_append]

theorem cnt2_append (a b : List (List ℕ)) : cnt2 (a ++ b) = cnt2 a + cnt2 b := by
  simp [cnt2, List.filter_append]

theorem rowsT_length : rowsT.length = 4608 := by
  simp only [rowsT, List.length_append, rowsT0_len, rowsT1_len, rowsT2_len, rowsT3_len, rowsT4_len, rowsT5_len, rowsT6_len, rowsT7_len, rowsT8_len, rowsT9_len, rowsT10_len, rowsT11_len]

theorem rowsT_cntC2 : cntC2 rowsT = 192 := by
  simp only [rowsT, cntC2_append, (rowsT0_cnt).2.1, (rowsT1_cnt).2.1, (rowsT2_cnt).2.1, (rowsT3_cnt).2.1, (rowsT4_cnt).2.1, (rowsT5_cnt).2.1, (rowsT6_cnt).2.1, (rowsT7_cnt).2.1, (rowsT8_cnt).2.1, (rowsT9_cnt).2.1, (rowsT10_cnt).2.1, (rowsT11_cnt).2.1]

theorem rowsT_cntC4 : cntC4 rowsT = 16 := by
  simp only [rowsT, cntC4_append, (rowsT0_cnt).2.2.1, (rowsT1_cnt).2.2.1, (rowsT2_cnt).2.2.1, (rowsT3_cnt).2.2.1, (rowsT4_cnt).2.2.1, (rowsT5_cnt).2.2.1, (rowsT6_cnt).2.2.1, (rowsT7_cnt).2.2.1, (rowsT8_cnt).2.2.1, (rowsT9_cnt).2.2.1, (rowsT10_cnt).2.2.1, (rowsT11_cnt).2.2.1]

theorem rowsT_cnt1 : cnt1 rowsT = 8 := by
  simp only [rowsT, cnt1_append, (rowsT0_cnt).2.2.2.1, (rowsT1_cnt).2.2.2.1, (rowsT2_cnt).2.2.2.1, (rowsT3_cnt).2.2.2.1, (rowsT4_cnt).2.2.2.1, (rowsT5_cnt).2.2.2.1, (rowsT6_cnt).2.2.2.1, (rowsT7_cnt).2.2.2.1, (rowsT8_cnt).2.2.2.1, (rowsT9_cnt).2.2.2.1, (rowsT10_cnt).2.2.2.1, (rowsT11_cnt).2.2.2.1]

theorem rowsT_cnt2 : cnt2 rowsT = 368 := by
  simp only [rowsT, cnt2_append, (rowsT0_cnt).2.2.2.2, (rowsT1_cnt).2.2.2.2, (rowsT2_cnt).2.2.2.2, (rowsT3_cnt).2.2.2.2, (rowsT4_cnt).2.2.2.2, (rowsT5_cnt).2.2.2.2, (rowsT6_cnt).2.2.2.2, (rowsT7_cnt).2.2.2.2, (rowsT8_cnt).2.2.2.2, (rowsT9_cnt).2.2.2.2, (rowsT10_cnt).2.2.2.2, (rowsT11_cnt).2.2.2.2]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
