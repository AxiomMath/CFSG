module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Thm22
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.RankOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Lemma15Guarded
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.LayerBalanceAt

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open CFSG.EvenSporadicStandard.Induction

theorem sol78Thm22Hered_proved_of_lemma15 (h13 : FS79Thm13UseHered) (h15 : FS79Lemma15Hered) :
    Sol78Thm22Hered :=
  fun H _ _ hH =>
    sol78Thm22At_of_balance (h13 H hH) (layerBalanceKAt_of_lemma15At (h15 H hH))
      sol78RankOne_proved

end CFSG.EvenSporadicStandard.Induction.Junction
