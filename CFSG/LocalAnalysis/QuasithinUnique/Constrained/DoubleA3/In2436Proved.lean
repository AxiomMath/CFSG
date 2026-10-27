module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabClass8Split
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNative
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTitsProof
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeProp121
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519

theorem in2436_i32 : LemmaI32 := I32.lemmaI32

theorem in2436_p121_3
    : Prop121Three :=
  Vol2Native.prop121Three_of_a3 Vol2Native.a37ForSQTKCat_proved
    (Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)

theorem in2436_p121_5
    : Prop121Five :=
  Vol2Native.prop121Five_of_core Vol2Native.a36CoreForSQTKCat_proved
    CFSG.Quasithin.l2MultiplierFact

theorem in2436_threeRank
    : TabThreeRank := tabThreeRank_of lemma122Rank tabThreeRankNine

theorem in2436_list115
    (hJ4 : Ch1.J4OutOdd) (hTC : Ch1.TitsTwoCoverTrivial) :
    Lemma115_3_List :=
  lemma115_3_List_of_rest_inputs' K1.titsSylowCentralizingAutInner
    (Ch1.sporadicRestAutInner_of_J4OutOdd hJ4) hTC

theorem inputs2436Core_of_ident
    (hJ4 : Ch1.J4OutOdd) (hTC : Ch1.TitsTwoCoverTrivial)
    (hident : TabIdentA6) : Inputs2436Core :=
  ⟨in2436_i32, in2436_p121_3, in2436_p121_5, in2436_list115 hJ4 hTC, in2436_threeRank, hident⟩

end CFSG.QuasithinUnique.DoubleA3
