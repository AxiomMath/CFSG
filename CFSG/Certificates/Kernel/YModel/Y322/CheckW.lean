module

public import CFSG.Certificates.Kernel.YModel.Y322.Rows
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 100000

#kc_unfold CFSG.KD.YMY322.w_f12 CFSG.KD.YMY322.Rows.chkW0 0
  eval CFSG.KD.YMY322.Rows.W0P CFSG.KD.YMY322.Rows.wordW0a CFSG.KD.YMY322.Rows.wordW0b
#kc_each_unfold CFSG.KD.YMY322.Rows.chkW0 0 8 as CFSG.KD.YMY322.w_fc at 1
  eval CFSG.KD.YMY322.Rows.W0P CFSG.KD.YMY322.Rows.wordW0a CFSG.KD.YMY322.Rows.wordW0b
#kc_unfold CFSG.KD.YMY322.w_ff CFSG.KD.YMY322.Rows.chkW0 9
  eval CFSG.KD.YMY322.Rows.W0P CFSG.KD.YMY322.Rows.wordW0a CFSG.KD.YMY322.Rows.wordW0b

end
