module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Done
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47RDone
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47SL2eMain

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer

theorem prop4_7S_modulo_e (h42 : Prop4_2) (hL : Lemma31Narrow)
    (hG : NonCentralDihedral) (h29 : Lemma29First) (he : P47BranchSL2e) : Prop4_7S :=
  prop4_7S_of_branchC h42 hL (prop47R_of_lemma29First hG h29)
    (p47BranchSL2_of p47SL2b_thm he)

theorem prop4_7S_proved (h42 : Prop4_2) (hL : Lemma31Narrow)
    (hG : NonCentralDihedral) (h29 : Lemma29First) : Prop4_7S :=
  prop4_7S_modulo_e h42 hL hG h29 p47SL2e_thm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
