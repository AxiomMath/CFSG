module

public import CFSG.Certificates.Kernel.YModel.Y322.Rows
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 100000

#kc_each_unfold CFSG.KD.YMY322.Rows.chkC0 0 7 as CFSG.KD.YMY322.c0_l
  eval CFSG.KD.YMY322.Rows.C0P
#kc_each_unfold CFSG.KD.YMY322.Rows.chkC1 0 6 as CFSG.KD.YMY322.c1_l
  eval CFSG.KD.YMY322.Rows.C1P

end
