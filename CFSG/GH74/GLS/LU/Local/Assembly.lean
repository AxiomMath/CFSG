module

public import CFSG.GH74.GLS.LU.Local.Leaves
public import CFSG.GH74.GLS.LU.Local.SL2Sylow

public section

namespace CFSG.GH74.GLS.LU.Local

theorem luGenLeaf : LUGenLeaf := luGenLeaf_of_sl2 SL2.sl2SylowLeaf

theorem luLocalLeaf_of_A3
    (hA3 : LUA3Leaf) : LULocalLeaf :=
  luLocalLeaf_of_leaves luGenLeaf hA3

theorem luNeighborhood_of_A3
    (hM : LUModelLeaf) (hA3 : LUA3Leaf) (h6A : LUMax6A) :
    LUNeighborhood :=
  luNeighborhood_of_leaves hM luGenLeaf hA3 h6A

end CFSG.GH74.GLS.LU.Local
