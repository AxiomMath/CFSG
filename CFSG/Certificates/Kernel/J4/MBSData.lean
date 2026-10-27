module

public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Y333.Dispatch
public import CFSG.Certificates.Kernel.J4.DceS
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_decls CFSG.KJ4.MBS "CFSG/Certificates/Kernel/J4/data/MBS_const.txt" 4096023
  15495531560495245530

#kc_natDispatch CFSG.KJ4.MBS.HTB CFSG.KJ4.MBS.HT_B 94 4
#kc_natDispatch CFSG.KJ4.MBS.OTB CFSG.KJ4.MBS.OT_B 60 4
#kc_natDispatch CFSG.KJ4.MBS.FTB CFSG.KJ4.MBS.FT_B 310 4
#kc_natDispatch CFSG.KJ4.MBS.WT CFSG.KJ4.MBS.WT_ 11 4
#kc_natDispatch CFSG.KJ4.MBS.TW CFSG.KJ4.MBS.TW_ 89 4
#kc_natDispatch CFSG.KJ4.MBS.SG CFSG.KJ4.MBS.SG_ 186 4

public section

@[expose] noncomputable def CFSG.KJ4.MBS.HT (i : Nat) : Nat := CFSG.KJ4.S.tgetN CFSG.KJ4.MBS.HTB 324 6 5969 i
@[expose] noncomputable def CFSG.KJ4.MBS.OT (i : Nat) : Nat := CFSG.KJ4.S.tgetN CFSG.KJ4.MBS.OTB 360 6 3795 i
@[expose] noncomputable def CFSG.KJ4.MBS.FT (i : Nat) : Nat := CFSG.KJ4.S.tgetN CFSG.KJ4.MBS.FTB 644 6 19839 i

end
