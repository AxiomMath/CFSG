module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vData
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.XQW

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (1, false), (1, false), (1, false), (1, false)],
    [(0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false)],
    [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)],
    [(0, false), (0, false), (1, false), (0, true), (1, true), (1, true), (0, false), (0, false), (1, false), (0, true), (1, true), (1, true)],
    [(2, true), (2, true)],
    [(2, false), (0, false), (0, false), (1, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, true), (1, true), (2, true), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true)],
    [(2, true), (1, false), (0, false), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true), (1, true), (2, true), (1, false), (0, false), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, false), (0, false), (1, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, true), (1, true)],
    [(2, true), (1, false), (1, false), (0, true), (1, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (2, true), (1, false), (1, false), (0, true), (1, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (0, false), (1, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, true), (1, true)],
    [(2, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (0, false), (2, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (0, false), (0, false), (0, false), (1, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, true), (1, true)],
    [(2, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false), (0, false), (2, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false), (0, false), (0, false), (0, false), (1, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, true), (1, true)],
    [(2, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, true), (0, true), (1, false), (2, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, true), (0, true), (1, false), (2, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, true), (0, true), (1, false)],
    [(2, true), (1, false), (0, false), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true), (0, true), (1, true), (0, false), (2, true), (1, false), (0, false), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true), (0, true), (1, true), (0, false), (2, true), (1, false), (0, false), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true), (0, true), (1, true), (0, false)],
    [(2, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, false), (0, false), (1, true), (2, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, false), (0, false), (1, true), (2, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, false), (0, false), (1, true)],
    [(2, true), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (2, true), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (2, true), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false)],
    [(2, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false), (0, true), (0, true), (1, true), (2, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false), (0, true), (0, true), (1, true), (2, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false), (0, true), (0, true), (1, true)],
    [(2, true), (1, false), (1, false), (0, true), (1, true), (0, false), (1, true), (2, true), (1, false), (1, false), (0, true), (1, true), (0, false), (1, true), (2, true), (1, false), (1, false), (0, true), (1, true), (0, false), (1, true)],
    [(2, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (0, false), (1, true), (0, true), (2, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (0, false), (1, true), (0, true), (2, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (0, false), (1, true), (0, true)],
    [(2, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (2, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (2, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false)],
    [(2, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (2, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (2, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (2, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (2, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false)],
    [(2, true), (1, false), (1, false), (0, true), (1, true), (0, false), (0, false), (1, false), (0, false), (2, true), (1, false), (1, false), (0, true), (1, true), (0, false), (0, false), (1, false), (0, false), (2, true), (1, false), (1, false), (0, true), (1, true), (0, false), (0, false), (1, false), (0, false), (2, true), (1, false), (1, false), (0, true), (1, true), (0, false), (0, false), (1, false), (0, false), (2, true), (1, false), (1, false), (0, true), (1, true), (0, false), (0, false), (1, false), (0, false)],
    [(2, true), (1, false), (0, false), (1, true), (1, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (2, true), (1, false), (0, false), (1, true), (1, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (2, true), (1, false), (0, false), (1, true), (1, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (2, true), (1, false), (0, false), (1, true), (1, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (2, true), (1, false), (0, false), (1, true), (1, true), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false)],
    [(2, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (2, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (2, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (2, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (2, true), (1, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false)]]

#kb_table CFSG.KBRoute.XQW T1 XQW_T1v include_bytes "data/XQW_T1v.meta" 275056 5348060446428055382 197121 CFSG.KBRoute.XQW.rels "1 2"

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.XQW

end
