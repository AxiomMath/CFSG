module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.RankOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Closed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.LayerBalanceAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Lemma15Guarded

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open CFSG.EvenSporadicStandard.Induction

theorem sol78Cor23SHered_proved_of_lemma15 (h13 : FS79Thm13UseHered) (h15 : FS79Lemma15Hered) :
    Sol78Cor23SHered :=
  sol78Cor23SHered_of_balance h13 (fun G _ _ hG => layerBalanceKAt_of_lemma15At (h15 G hG))
    sol78RankOne_proved sol78ExcClosed_proved

end CFSG.EvenSporadicStandard.Induction.Junction
