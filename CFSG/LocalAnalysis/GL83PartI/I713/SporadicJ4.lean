module

public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.Sporadic.NativeFinite

public section

namespace GL83.I713

open CFSG.Blueprint

local instance finite_carrier_J4 : Finite (NativeSporadic.Carrier .J4) :=
  CFSG.Sporadic.finite_carrier_of_ne_M .J4 (by decide)

theorem outClauseFor_sporadic_J4 :
    OutClauseFor (NativeSporadic.Carrier .J4) :=
  outClauseFor_of_card_outer_le_four (CFSG.AGLEmbedding.card_outer_J4.le.trans (by norm_num))

end GL83.I713
