
module

import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Th.S.Chars
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

#th_chars CFSG.KD.ThTs.Lrows CFSG.Sporadic.ThSchreier.localRowsTxt
#th_chars_in CFSG.KD.ThTs.Lpx CFSG.Sporadic.ThSchreier.localPermX
#th_chars_in CFSG.KD.ThTs.Lpy CFSG.Sporadic.ThSchreier.localPermY
#th_chars_in CFSG.KD.ThTs.Ltp CFSG.Sporadic.ThSchreier.localTreePts
#th_chars_in CFSG.KD.ThTs.Ltpa CFSG.Sporadic.ThSchreier.localTreePar
#th_chars_in CFSG.KD.ThTs.Ltla CFSG.Sporadic.ThSchreier.localTreeLab

#kc_repo #kc_nat_items_gz CFSG.KD.ThTs "CFSG/Certificates/Kernel/Th/S/Data/data/Ts_const.items.gz"
    436304 11208376184523700696
    (R_ 0 33) (ROW_ 0 2457) (PX_ 0 2457) (PY_ 0 2457) (TP_ 0 2457) (TPA_ 0 2457) (TLA_ 0 2457) (INV_
    0 2457) (SR_ 0 3)
#kc_select CFSG.KD.ThTs RB R_ 33
#kc_select CFSG.KD.ThTs ROWS ROW_ 2457
#kc_select CFSG.KD.ThTs PX PX_ 2457
#kc_select CFSG.KD.ThTs PY PY_ 2457
#kc_select CFSG.KD.ThTs TP TP_ 2457
#kc_select CFSG.KD.ThTs TPA TPA_ 2457
#kc_select CFSG.KD.ThTs TLA TLA_ 2457
#kc_select CFSG.KD.ThTs INV INV_ 2457
