module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Thm
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.L63Thm
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cIMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NCDProved
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EFinal
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutC
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutD1H

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.L64

open CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage1.Main

theorem lemma6_4_thm
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Stage12.Kind) (S : Subgroup G),
      Stage2Ctx G z k S → L4TwoFieldStmt G z k S)
    (hSch : P34.GHSchreier) (h29 : Lemma29First) (h43 : Prop4_3E) : Lemma6_4 :=
  lemma6_4_of
    (lemma6_3_thm (prop4_1c_of_fullG (nonCentralDihedral_of_ctx hfld hSch) (prop4_1c_i_of h29)))
    (L46E.lemma4_6E_of h43 L46E.autFactCOdd_thm L46E.autFactD1_proved)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.L64
