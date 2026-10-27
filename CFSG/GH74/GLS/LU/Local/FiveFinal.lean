module

public import CFSG.GH74.GLS.LU.Local.FiveL66o
public import CFSG.GH74.GLS.LU.Local.FiveL84
public import CFSG.GH74.GLS.LU.Local.FiveL85
public import CFSG.GH74.GLS.LU.Local.FiveL86
public import CFSG.GH74.GLS.LU.Local.FiveL88
public import CFSG.GH74.GLS.LU.Local.FiveL89
public import CFSG.GH74.GLS.LU.Local.FiveStdFinal

public section

open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU

namespace CFSG.GH74.GLS.LU.Local.Five

theorem luA3Five'_of_model
    (hB : FiveModelBaseLeaf) (hM : FiveModelLeaf) (h84'' : Leaf84'') : LUA3Five' :=
  luA3Five'_of_leaves (leaf66_of_model hB hM) (leaf82_of_model hB hM) leaf83
    (leaf84_of_parts leaf84' h84'') leaf85 leaf86 leaf87 leaf88 leaf89

theorem luA3Five'_of_certificate
    (h84'' : Leaf84'') : LUA3Five' :=
  luA3Five'_of_model fiveModelLeaves_of_check.1 fiveModelLeaves_of_check.2 h84''

end CFSG.GH74.GLS.LU.Local.Five
