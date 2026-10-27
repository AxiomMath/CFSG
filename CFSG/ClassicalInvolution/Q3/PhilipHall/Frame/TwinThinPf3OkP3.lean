module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FastP3A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FastP3B1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FastP3B2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem fastOk_P3 : dataP3.FastOk where
  ha := (mem_aeSubOver_of _ (mem_P3 _ (by simp)))
  hb := (mem_aeSubOver_of _ (mem_P3 _ (by simp)))
  hc := (mem_aeSubOver_of _ (mem_P3 _ (by simp)))
  hd := (mem_aeSubOver_of _ (mem_P3 _ (by simp)))
  hh := (mem_aeSubOver_of _ (mem_P3 _ (by simp)))
  rels_h := rels_h_P3
  rels_cands := rels_cands_P3
  cand_words := cand_words_P3
  dyn := dyn_P3
  perm_filter := perm_filter_P3
  filter_ok := filter_ok_P3
  perm_chk := perm_chk_P3
  permWords_ok := permWords_ok_P3
  pairWords_ok := pairWords_ok_P3
  pairs_cov := pairs_cov_P3

theorem ok_P3 : dataP3.Ok := PairData.Ok_of_fast fastOk_P3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
