module

public import CFSG.GH74.Generic.S1.ExoticGlue
public import CFSG.GH74.Generic.S1.UniFull

public section

namespace CFSG.GH74.Generic.S1

open CFSG.Assembly.LowTwoRank

theorem uniClassify : UniClassify :=
  fun _ _ _ _ hF hq α hα hout => classify_uni hF hq α hα hout

theorem graphUniRefine : GraphUniRefine :=
  fun _ _ _ _ hF hq α hα h => graphField_uni hF hq α hα h

end CFSG.GH74.Generic.S1
