module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47C
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47FldMain

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer

theorem p47BranchC_thm : P47BranchC := p47BranchC_of p47FieldCase_thm

theorem prop4_7S_of_branchC (h42 : Prop4_2) (hL : Lemma31Narrow)
    (hR : Prop47R) (hSL2 : P47BranchSL2) : Prop4_7S :=
  prop4_7S_of h42 hL hR hSL2 p47BranchC_thm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
