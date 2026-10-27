module

public import CFSG.Quasithin.EmptyFaithful.S14612GC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S14612DC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S14612F0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure NoE9Z4Res_F4 : Prop where

  min : NoE9Z4Min

  big : NoE9Z4Large_F4

theorem noE9Z4_of_res_F4 (h35 : Lemma1435) (h5 : Stage1461Five) (r : NoE9Z4Res_F4) : NoE9Z4_F4 := by
  intro G _ _ T M S H PQ p hred hmax hshape
  have hle := IsE9Z4Shape.two_pow_nine_le h35 h5 S hred hshape
  rcases hle.lt_or_eq with hlt | heq
  · exact r.big G T M S H PQ p hred hmax hshape hlt
  · obtain ⟨h1, h2, h3, h4, h5'⟩ := IsE9Z4Shape.equality_case h35 h5 S hred hshape heq.symm
    exact r.min G T M S H PQ p hred hmax hshape heq.symm h1 h2 h3 h4 h5'

end CFSG.Quasithin
