module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vData
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.CJHe0

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(3, true), (3, true)],
    [(0, true), (0, true), (0, true), (0, true)],
    [(0, true), (2, false), (0, true), (2, false)],
    [(0, true), (3, true), (0, true), (3, false)],
    [(1, true), (1, true), (1, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, false), (2, false), (2, false)],
    [(0, true), (2, true), (0, true), (3, true), (2, false), (3, true)],
    [(1, true), (2, true), (1, true), (2, false), (2, false), (2, false)],
    [(1, true), (2, false), (3, true), (1, true), (2, false), (3, false)],
    [(1, true), (3, true), (2, true), (1, true), (3, false), (2, true)],
    [(2, true), (2, true), (3, true), (2, false), (2, false), (3, false)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(4, true), (4, true), (4, true)],
    [(0, true), (3, true), (4, true), (0, false), (3, false), (4, false)],
    [(1, true), (4, true), (1, true), (4, false), (3, true), (4, true), (2, false)],
    [(0, true), (0, true), (1, true), (4, true), (0, false), (2, true), (4, false), (1, true)],
    [(5, true), (5, true), (5, true)],
    [(0, true), (2, false), (2, false), (5, true), (0, true), (5, false)],
    [(0, true), (0, true), (1, true), (3, true), (5, false), (1, true), (5, false)],
    [(1, true), (1, true), (3, true), (5, false), (2, false), (1, true), (5, true)],
    [(1, true), (4, true), (5, false), (4, false), (5, false), (2, true), (4, false), (5, true)],
    [(7, true), (7, true), (7, true)],
    [(0, true), (6, false), (0, true), (6, false)],
    [(0, true), (7, true), (1, true), (3, true), (7, true)],
    [(0, true), (1, true), (1, true), (7, true), (2, false), (7, true)],
    [(0, true), (1, true), (7, true), (1, false), (6, true), (7, false), (2, false)],
    [(2, true), (4, true), (3, true), (7, false), (4, false), (6, false), (4, false), (6, true), (4, true), (6, false)],
    [(0, true), (6, true), (7, true), (5, false), (7, true), (5, true), (7, true), (5, false), (7, false), (5, true), (2, true)]]

#kb_table CFSG.KBRoute.CJHe0 T1 CJHe0_T1v include_bytes "data/CJHe0_T1v.meta" 70638 7457101188361676601 578437695752307201 CFSG.KBRoute.CJHe0.rels "1 2 3 4 5 7 8"

theorem top : KB.topOk T1.amap (nat_lit 8) = true := by quickRfl

end CFSG.KBRoute.CJHe0

end
