module

public import CFSG.GH74.Generic.BProg.B3.KG531Basic
public import CFSG.GH74.Generic.BProg.B3.KG531Ord
public import CFSG.GH74.Generic.BProg.B3.KG531L4
public import CFSG.GH74.Generic.BProg.B3.KG531U4
public import CFSG.GH74.Generic.BProg.B3.KG531Sp4
public import CFSG.GH74.Generic.BProg.B3.KG531L5
public import CFSG.GH74.Generic.BProg.B3.KG531L2

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

theorem kg531Leaves :
    KG531Leaves :=
  ⟨kg531_alt, kg531_m11, kg531_m12, kg531_m22, kg531_m23, kg531_j1, kg531_j2, kg531_j3, kg531_mcl,
    kg531_ly, kg531_l2, kg531_l3, kg531_u3, kg531_sp4, kg531_g2, kg531_d4, kg531_l4, kg531_u4,
    kg531_l5, kg531_u5, kg531_ree, kg531_l28, kg531_l216, kg531_l34, kg531_u34, kg531_sz8⟩

theorem kg531Table :
    KG531Table :=
  kg531Table_of_leaves kg531Leaves

end CFSG.GH74.Generic.BProg.B3
