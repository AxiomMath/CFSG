module

public import CFSG.Quasithin.EmptyFaithful.S146zMDec
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S14612DC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146F13

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem input14614Sol_of_dec_F4 (h12 : Stage14612PartP_F4) (i : Input14614SolDec) : Input14614Sol_F4 := by
  intro G _ _ T M S H PQ p hred hmax hp3 hK
  exact i G T M S H PQ p hred hmax hp3 (h12 G T M S H PQ p hred hmax).2 hK

end CFSG.Quasithin
