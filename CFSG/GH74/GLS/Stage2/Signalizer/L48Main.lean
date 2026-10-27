module

public import CFSG.GH74.GLS.Stage2.Signalizer.L48Reduce
public import CFSG.GH74.GLS.Stage2.Signalizer.L48StarParts
public import CFSG.GH74.GLS.Stage2.Signalizer.L48Alt
public import CFSG.GH74.GLS.Stage2.Signalizer.L48Sl2Prod
public import CFSG.GH74.GLS.Stage2.Signalizer.L48Sl2Key
public import CFSG.GH74.GLS.Stage2.Signalizer.L199

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

theorem star48_thm : Star48 :=
  star48_of_parts
    (fun hn8 hn11 hK t ht2 p hp hp2 Y hY hN hc => star_twoAlt hn8 hn11 hK t ht2 p hp hp2 Y hY hN hc)
    (fun L₁ L₂ r₁ r₂ hc h1 h2 ho1 ho2 t htL ht2 p hp hp2 Y hYp hYL hN hcomm =>
      star_sl2_sl2 sl2Key L₁ L₂ r₁ r₂ hc h1 h2 ho1 ho2 t htL ht2 p hp hp2 Y hYp hYL hN hcomm)

theorem lemma4_8w_thm : Lemma4_8w :=
  lemma4_8w_of_star CFSG.GH74.GLS.Stage2.Signalizer.L199.ig_19_9 star48_thm

end CFSG.GH74.GLS.Stage2.Signalizer.L48
