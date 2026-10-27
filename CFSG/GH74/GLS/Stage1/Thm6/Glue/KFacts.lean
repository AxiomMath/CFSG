module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129b
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.IP
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Setting

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type*} [Group G] [Finite G]

structure KFacts (x : G) (S T P Q Rd F U : Subgroup G) : Prop where
  base : HBase G x S T P Q Rd F
  hu : HU S T U
  P_four : IP_P_four P
  outer : IP_outer x T Rd
  cent_four : IP_cent_four T P Q Rd
  Rd_factor : IP_Rd_factor T P Q Rd
  Rd_cyclic : IP_Rd_cyclic T Rd
  P_trans : IP_P_trans P Q Rd
  cent_Rd : IP_cent_Rd P Q Rd
  cent_P_exp : IP_cent_P_exp T P Q
  f3 : IP_f3 x P
  P_closed : IP_P_closed x T P
  P_conj : ∀ z : G, HZ T P z → IP_P_conj x z P
  z_V : ∀ z : G, HZ T P z → IP_z_V z P
  E8_two : Q = Subgroup.zpowers x → omega1 T ≤ Rd → IP_E8_two T
  Rd_dihedral : Q = Subgroup.zpowers x → IP_Rd_dihedral x Rd
  Rd_fuse : Q = Subgroup.zpowers x → IP_Rd_fuse x P Rd
  T_normal : ∀ z : G, HZ T P z → Q = Subgroup.zpowers x → omega1 T ≤ Rd → IP_T_normal x z T P Rd

end CFSG.GH74.GLS.Stage1.Thm6.Glue
