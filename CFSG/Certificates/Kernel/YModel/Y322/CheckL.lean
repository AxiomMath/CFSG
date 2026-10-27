module

public import CFSG.Certificates.Kernel.YModel.Y322.Rows
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 100000

#kc_each_unfold CFSG.KD.YMY322.Rows.chkL0 0 8 as CFSG.KD.YMY322.l
  eval CFSG.KD.YMY322.Rows.L0P
#kc_each_unfold CFSG.KD.YMY322.Rows.chkL1 0 8 as CFSG.KD.YMY322.e
  eval CFSG.KD.YMY322.Rows.L1P

end
