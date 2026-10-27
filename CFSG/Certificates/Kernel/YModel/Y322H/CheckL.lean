module

public import CFSG.Certificates.Kernel.YModel.Y322H.Rows
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 100000

#kc_each_unfold CFSG.KD.YMY322H.Rows.chkL0 0 8 as CFSG.KD.YMY322H.l
  eval CFSG.KD.YMY322H.Rows.L0P
#kc_each_unfold CFSG.KD.YMY322H.Rows.chkL1 0 8 as CFSG.KD.YMY322H.e
  eval CFSG.KD.YMY322H.Rows.L1P

end
