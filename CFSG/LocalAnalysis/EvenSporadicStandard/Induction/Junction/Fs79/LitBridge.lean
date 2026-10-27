module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Thm22Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Thm21Final

public section

namespace CFSG.EvenSporadicStandard.Induction

theorem Sol78LitCore.toLit (c : Sol78LitCore) : Sol78Lit :=
  { c with
    thm21 := Junction.sol78Thm21Hered_of_lemma15 c.fs79lemma15
    cor23 := Junction.sol78Cor23SHered_proved_of_lemma15 c.fs79thm13 c.fs79lemma15
    thm22 := Junction.sol78Thm22Hered_proved_of_lemma15 c.fs79thm13 c.fs79lemma15 }

end CFSG.EvenSporadicStandard.Induction
