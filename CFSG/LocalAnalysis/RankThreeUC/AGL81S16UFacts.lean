module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UFix
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16TsIdx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UStruct

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup

theorem u4ModuleFacts : U4ModuleFacts := by
  intro G _ _ p n M L V d hp hpq hn hLM hVM hML hMV
  exact
    { card_V := d.card_V
      nonsing_good := d.nonsing_good hp hpq hn hLM hMV
      p_dvd := d.p_dvd hp hpq hn hLM hMV
      ts_index := d.ts_index hn
      inv_index := fun t ht _ hnc => d.inv_index hLM hML hMV t ht hnc
      Q_le := fun A hAM hAab _ hQ => d.Q_le hn hLM hML hMV A hAM hAab hQ
      dim_F := fun B hBM hBL => d.dim_F hLM hMV hBM hBL
      ts_plane := d.ts_plane hn hLM hMV
      transvection := d.transvection hn hLM hMV
      rank_le := d.rank_le hn hLM hMV
      generation := d.generation hn hLM hMV }

end CFSG.LocalAnalysis.RankThreeUC
