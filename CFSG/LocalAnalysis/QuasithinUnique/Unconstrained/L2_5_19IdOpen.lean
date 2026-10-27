module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNative
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabA2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19L2pGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTitsProof
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeProp121
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Id
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdTabCover

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

theorem inputs2519Three_of_open
    (hJ4 : Ch1.J4OutOdd) (hTC : Ch1.TitsTwoCoverTrivial)
    (hident : TabIdent) (hHS : TabAutCentHS) (hHSc : TabHSCover) : Inputs2519Three where
  i32 := I32.lemmaI32
  p121_3 := Vol2Native.prop121Three_of_a3 Vol2Native.a37ForSQTKCat_proved
    (Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
  p121_5 := Vol2Native.prop121Five_of_core Vol2Native.a36CoreForSQTKCat_proved
    CFSG.Quasithin.l2MultiplierFact
  list115 := lemma115_3_List_of_rest_inputs' K1.titsSylowCentralizingAutInner
    (Ch1.sporadicRestAutInner_of_J4OutOdd hJ4) hTC
  cover := tabCover
  ident := hident
  autCent := Tab.tabAutCent
  autCentHS := hHS
  threeRank := tabThreeRank_of lemma122Rank tabThreeRankNine
  nonEmbed := tabNonEmbed_of_residual Tab.j2NoL34Component
  conj := Tab.tabConj
  j2cover := Tab.tabJ2Cover
  hscover := hHSc

theorem lemma2519_of_open
    (hJ4 : Ch1.J4OutOdd) (hTC : Ch1.TitsTwoCoverTrivial)
    (hident : TabIdent) (hHS : TabAutCentHS) (hHSc : TabHSCover) : Lemma2519 :=
  lemma2519_of_inputs (inputs2519Three_of_open hJ4 hTC hident hHS hHSc) part2_2519

end CFSG.QuasithinUnique.Id2519
