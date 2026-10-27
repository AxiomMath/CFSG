module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt6

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.L63

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

theorem lemma6_3_of_6_4 (h64 : Lemma6_4) : Lemma6_3 := by
  intro G _ _ z k S M p hC N A B r hH
  refine le_trans ?_ (h64 G z k S M p hC N A B r hH)
  exact Subgroup.map_mono le_sup_left

end CFSG.GH74.GLS.Stage2.Bender.Thm1.L63
