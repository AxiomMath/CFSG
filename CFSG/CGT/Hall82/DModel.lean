module

public import CFSG.CGT.Hall82.DModelA
public import CFSG.CGT.Hall82.DModelB
public import CFSG.CGT.Hall82.DModelC

public section

namespace CFSG.CGT.Hall82

theorem dModelFacts :
    DModelFacts where
  lin := DModel.lin
  oval_trans := DModel.oval_trans
  five_trans := DModel.five_trans
  five_not_oval := DModel.five_not_oval
  card_stab_oval := DModel.card_stab_oval
  card_stab := DModel.card_stab
  card_stabL_oval := DModel.card_stabL_oval
  card_stabL := DModel.card_stabL
  eq_bot_of_oval := DModel.eq_bot_of_oval
  rm_mul := DModel.rm_mul
  rm_inj := DModel.rm_inj
  mem_rm_iff := DModel.mem_rm_iff
  rm_le := DModel.rm_le
  rm_fix := DModel.rm_fix
  rm_not_le := DModel.rm_not_le
  le_rm := DModel.le_rm
  rm_le_or_quad := DModel.rm_le_or_quad
  u_inv := DModel.u_inv
  rm_comm_u := DModel.rm_comm_u
  rm_eq_zero_of_fix_u := DModel.rm_eq_zero_of_fix_u
  fix_rm := DModel.fix_rm
  u_maximal := DModel.u_maximal
  zeta_fix := DModel.zeta_fix
  zeta_pow := DModel.zeta_pow
  zeta_ne := DModel.zeta_ne
  zeta_conj := DModel.zeta_conj
  lift := DModel.lift
  xcode_mul := DModel.xcode_mul
  xcode_eq_zero := DModel.xcode_eq_zero
  xcode_surj := DModel.xcode_surj
  xcode_sq := DModel.xcode_sq
  xcode_orb := DModel.xcode_orb
  xcode_conj := DModel.xcode_conj
  xcode_conj_surj := DModel.xcode_conj_surj
  reducible := DModel.reducible

end CFSG.CGT.Hall82
