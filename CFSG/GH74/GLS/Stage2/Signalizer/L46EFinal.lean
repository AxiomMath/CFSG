module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EMain
public import CFSG.GH74.GLS.Stage2.Signalizer.L46ELayer
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutE
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutB

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

theorem lemma4_6E_of_aut (h43 : Prop4_3E) (hB : AutFactB) (hC : AutFactCOdd) (hD1 : AutFactD1H)
    (hE : AutFactE) : Lemma4_6E :=
  lemma4_6E_core (fun hD X E hEX hcomm => centralizes_commutator_layer hD X E hEX hcomm) h43 hB hC
    hD1 hE

theorem lemma4_6E_of_BCD (h43 : Prop4_3E) (hB : AutFactB) (hC : AutFactCOdd) (hD1 : AutFactD1H) :
    Lemma4_6E :=
  lemma4_6E_of_aut h43 hB hC hD1 autFactE

theorem lemma4_6E_of (h43 : Prop4_3E) (hC : AutFactCOdd) (hD1 : AutFactD1H) : Lemma4_6E :=
  lemma4_6E_of_BCD h43 autFactB hC hD1

end CFSG.GH74.GLS.Stage2.Signalizer.L46E
