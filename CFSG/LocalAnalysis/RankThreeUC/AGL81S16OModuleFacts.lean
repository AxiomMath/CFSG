module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OParE
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutT
public import CFSG.LocalAnalysis.RankThreeUC.AGL81Section16Reduced
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OChief
public import CFSG.HardMathSupport.U4FF.ClassMain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OTrans

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup

theorem o6ModuleFacts : O6ModuleFacts := by
  intro G _ _ p n M L V d hp hpq hn hLM _ hML hMV
  exact
    { card_V := d.card_V
      nonsing_good := d.nonsing_good hp hpq hn hLM hMV
      p_dvd := d.p_dvd hp hpq hn hLM hMV
      ts_index := d.ts_index hn
      ts_equal := d.ts_equal hp hpq hn hLM hMV
      transvection := d.transvection hn hLM hML hMV
      outer_nonsing := d.outer_nonsing hn hLM hML hMV
      outer_rank := fun A hAM hA hAL => d.outer_rank hn hLM hML hMV hAM hA hAL
      parabolic := d.parabolic hp hpq hn hLM hML hMV }

end CFSG.LocalAnalysis.RankThreeUC

namespace CFSG.Yardstones.M9cbf837c48cf

theorem agl81TheoremDSection16_proved :
    AGL81TheoremDSection16Statement :=
  agl81TheoremDSection16_of_dichotomy CFSG.HardMathSupport.U4FF.u4RankDichotomy_holds
      CFSG.LocalAnalysis.RankThreeUC.o6ModuleFacts LocalAnalysis.RankThreeUC.o6ChiefFacts

end CFSG.Yardstones.M9cbf837c48cf
