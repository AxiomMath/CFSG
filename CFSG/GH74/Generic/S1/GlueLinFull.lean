module

public import CFSG.GH74.Generic.S1.ExoticGlue
public import CFSG.GH74.Generic.S1.LinGraph

public section

namespace CFSG.GH74.Generic.S1

open CFSG.Assembly.LowTwoRank

theorem graphLinRefine : GraphLinRefine :=
  fun _ _ _ hF α hα h => graphLike_lin hF α hα h

end CFSG.GH74.Generic.S1
