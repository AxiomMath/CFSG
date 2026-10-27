module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FastP1A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FastP1B1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FastP1B2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem fastOk_P1 : dataP1.FastOk where
  ha := (mem_aeSubOver_of _ (mem_P1 _ (by simp)))
  hb := (mem_aeSubOver_of _ (mem_P1 _ (by simp)))
  hc := (mem_aeSubOver_of _ (mem_P1 _ (by simp)))
  hd := (mem_aeSubOver_of _ (mem_P1 _ (by simp)))
  hh := (mem_aeSubOver_of _ (mem_P1 _ (by simp)))
  rels_h := rels_h_P1
  rels_cands := rels_cands_P1
  cand_words := cand_words_P1
  dyn := dyn_P1
  perm_filter := perm_filter_P1
  filter_ok := filter_ok_P1
  perm_chk := perm_chk_P1
  permWords_ok := permWords_ok_P1
  pairWords_ok := pairWords_ok_P1
  pairs_cov := pairs_cov_P1

theorem ok_P1 : dataP1.Ok := PairData.Ok_of_fast fastOk_P1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
