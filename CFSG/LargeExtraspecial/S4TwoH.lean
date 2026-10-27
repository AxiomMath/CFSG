module

public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_PSL_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {n p f : ℕ} (h : StatedClassicalModel B .PSL n p f) : StatedClassicalModel A .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem nonempty_mulEquiv_psl_of_alternating_eight {A : Type} [Group A]
    (e : A ≃* alternatingGroup (Fin 8)) :
    Nonempty (A ≃* StatedProj (StatedSL 4 (ZMod 2))) :=
  CFSG.GH74.Exceptional.nonempty_mulEquiv_statedProj_of_alternating_eight e

end CFSG.LargeExtraspecial.S4
