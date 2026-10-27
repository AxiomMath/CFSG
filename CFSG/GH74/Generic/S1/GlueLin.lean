module

public import CFSG.GH74.Generic.S1.Glue
public import CFSG.GH74.Generic.S1.LinClassify

public section

namespace CFSG.GH74.Generic.S1

open CFSG.Assembly.LowTwoRank

theorem linClassify : LinClassify :=
  fun _ _ _ hF α hα hout => classify_lin hF α hα hout

end CFSG.GH74.Generic.S1
