module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0Rows0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0Rows1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0Rows2

public section

set_option maxRecDepth 100000

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K

@[expose] def rowsAll : List (List ℕ) :=
  rows0 ++
  rows1 ++
  rows2 ++
  rows3 ++
  rows4 ++
  rows5 ++
  rows6 ++
  rows7 ++
  rows8 ++
  rows9 ++
  rows10 ++
  rows11

theorem chk_chunk (rs ss : List (List ℕ)) (prev fin : ℕ) (h : chkTo prev fin rs = true)
    (h2 : chk fin ss = true) : chk prev (rs ++ ss) = true := by
  obtain ⟨h1, h3⟩ := chkTo_iff rs prev fin h
  exact (chk_append rs ss prev).2 ⟨h1, by rw [h3]; exact h2⟩

theorem rowsAll_chk : chk 0 rowsAll = true := by
  have h11 := (chkTo_iff _ _ _ rows11_chk).1
  have h10 := chk_chunk _ _ _ _ rows10_chk h11
  have h9 := chk_chunk _ _ _ _ rows9_chk h10
  have h8 := chk_chunk _ _ _ _ rows8_chk h9
  have h7 := chk_chunk _ _ _ _ rows7_chk h8
  have h6 := chk_chunk _ _ _ _ rows6_chk h7
  have h5 := chk_chunk _ _ _ _ rows5_chk h6
  have h4 := chk_chunk _ _ _ _ rows4_chk h5
  have h3 := chk_chunk _ _ _ _ rows3_chk h4
  have h2 := chk_chunk _ _ _ _ rows2_chk h3
  have h1 := chk_chunk _ _ _ _ rows1_chk h2
  have h0 := chk_chunk _ _ _ _ rows0_chk h1
  exact h0

theorem cntE_append (a b : List (List ℕ)) : cntE (a ++ b) = cntE a + cntE b := by
  simp [cntE, List.filter_append]

theorem cntS_append (a b : List (List ℕ)) : cntS (a ++ b) = cntS a + cntS b := by
  simp [cntS, List.filter_append]

theorem rowsAll_length : rowsAll.length = 4608 := by
  simp only [rowsAll, List.length_append, rows0_len, rows1_len, rows2_len, rows3_len, rows4_len, rows5_len, rows6_len, rows7_len, rows8_len, rows9_len, rows10_len, rows11_len]

theorem rowsAll_cntE : cntE rowsAll = 8 := by
  simp only [rowsAll, cntE_append, rows0_cntE, rows1_cntE, rows2_cntE, rows3_cntE, rows4_cntE, rows5_cntE, rows6_cntE, rows7_cntE, rows8_cntE, rows9_cntE, rows10_cntE, rows11_cntE]

theorem rowsAll_cntS : cntS rowsAll = 192 := by
  simp only [rowsAll, cntS_append, rows0_cntS, rows1_cntS, rows2_cntS, rows3_cntS, rows4_cntS, rows5_cntS, rows6_cntS, rows7_cntS, rows8_cntS, rows9_cntS, rows10_cntS, rows11_cntS]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K
