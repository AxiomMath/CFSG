module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FastP2A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FastP2B1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FastP2B2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem fastOk_P2 : dataP2.FastOk where
  ha := (mem_aeSubOver_of _ (mem_P2 _ (by simp)))
  hb := (mem_aeSubOver_of _ (mem_P2 _ (by simp)))
  hc := (mem_aeSubOver_of _ (mem_P2 _ (by simp)))
  hd := (mem_aeSubOver_of _ (mem_P2 _ (by simp)))
  hh := (mem_aeSubOver_of _ (mem_P2 _ (by simp)))
  rels_h := rels_h_P2
  rels_cands := rels_cands_P2
  cand_words := cand_words_P2
  dyn := dyn_P2
  perm_filter := perm_filter_P2
  filter_ok := filter_ok_P2
  perm_chk := perm_chk_P2
  permWords_ok := permWords_ok_P2
  pairWords_ok := pairWords_ok_P2
  pairs_cov := pairs_cov_P2

theorem ok_P2 : dataP2.Ok := PairData.Ok_of_fast fastOk_P2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
