module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vData
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.XGRuP12t

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(2, true), (2, true)],
    [(3, true), (3, true)],
    [(7, true), (7, true)],
    [(6, true), (6, true), (6, true)],
    [(0, true), (1, true), (0, false), (1, true)],
    [(1, true), (1, true), (0, true), (0, true)],
    [(1, true), (0, false), (0, false), (1, true)],
    [(8, true), (0, false), (8, false), (0, true)],
    [(5, false), (0, false), (5, false), (0, false)],
    [(5, true), (0, false), (5, true), (0, false)],
    [(0, false), (4, false), (0, false), (4, false)],
    [(2, true), (3, true), (2, true), (3, true)],
    [(0, true), (4, false), (0, true), (4, false)],
    [(1, true), (6, true), (1, false), (6, false)],
    [(0, true), (6, true), (0, false), (6, false)],
    [(4, true), (6, true), (5, false), (6, false)],
    [(2, true), (6, true), (3, true), (6, false)],
    [(2, true), (6, true), (2, true), (6, false), (3, true)],
    [(6, true), (4, true), (6, false), (4, true), (5, true)],
    [(8, true), (8, true), (8, true), (0, true), (8, true), (0, true)],
    [(0, false), (4, false), (5, true), (4, true), (5, false), (0, false)],
    [(5, true), (8, true), (8, true), (5, true), (8, true), (8, true)],
    [(5, true), (4, false), (4, false), (1, false), (5, true), (1, true)],
    [(1, false), (2, true), (1, false), (2, true), (8, true), (0, true), (8, true)],
    [(4, false), (7, true), (4, true), (7, true), (1, false), (5, false), (1, true)],
    [(7, true), (2, true), (4, false), (7, true), (3, true), (5, false), (4, false)],
    [(0, false), (5, false), (1, false), (2, true), (0, true), (5, false), (1, true), (2, true)],
    [(7, true), (8, true), (6, true), (8, false), (6, false), (1, false), (8, false), (5, true)],
    [(8, true), (4, true), (3, true), (2, true), (8, false), (1, true), (5, true), (0, false)],
    [(2, true), (0, true), (5, false), (8, false), (2, true), (5, true), (8, false), (0, false)],
    [(8, true), (2, true), (8, true), (2, true), (8, true), (2, true), (8, true), (2, true)],
    [(4, false), (8, false), (4, false), (2, true), (0, false), (8, true), (1, true), (5, true), (0, false)],
    [(4, true), (5, true), (3, true), (1, true), (8, false), (5, true), (8, true), (5, false), (2, true)],
    [(2, true), (8, false), (2, true), (8, true), (0, false), (2, true), (8, false), (2, true), (0, false), (8, true)],
    [(3, true), (0, false), (5, false), (3, true), (2, true), (1, true), (2, true), (5, true), (1, false), (0, false)],
    [(0, false), (1, true), (5, false), (8, false), (5, true), (1, false), (0, false), (5, true), (8, false), (5, false)],
    [(0, false), (6, false), (7, true), (6, true), (7, true), (6, false), (3, true), (5, true), (0, true), (3, true)],
    [(7, true), (8, false), (8, false), (4, false), (7, true), (4, true), (2, true), (0, true), (5, false), (2, true)],
    [(1, true), (8, false), (5, true), (8, false), (2, true), (1, true), (8, false), (5, true), (8, false), (2, true)],
    [(2, true), (8, true), (0, false), (5, true), (8, false), (1, false), (4, true), (1, false), (3, true), (1, true), (0, true)],
    [(2, true), (0, true), (5, false), (2, true), (8, true), (3, true), (1, true), (3, true), (1, true), (8, true), (5, false)],
    [(7, true), (1, false), (7, true), (2, true), (1, false), (0, true), (5, true), (8, false), (5, false), (2, true), (8, false)],
    [(8, true), (2, true), (0, false), (1, true), (8, false), (5, false), (2, true), (8, true), (5, false), (8, true), (1, false)],
    [(8, true), (3, true), (1, true), (3, true), (4, true), (1, false), (3, true), (5, false), (1, false), (8, true), (2, true)],
    [(4, true), (0, false), (4, false), (5, true), (8, true), (2, true), (4, true), (0, true), (5, true), (4, false), (8, true), (2, true)],
    [(2, true), (8, false), (0, true), (1, false), (8, false), (5, false), (2, true), (8, false), (0, false), (1, true), (8, false), (5, false)],
    [(7, true), (8, true), (7, true), (8, false), (7, true), (0, true), (1, false), (8, false), (5, false), (1, false), (0, true), (5, false), (1, false)]]

#kb_table CFSG.KBRoute.XGRuP12t T1 XGRuP12t_T1v include_bytes "data/XGRuP12t_T1v.meta" 61445 3472798169210265517 166599134359138271745 CFSG.KBRoute.XGRuP12t.rels ""

theorem top : KB.topOk T1.amap (nat_lit 9) = true := by quickRfl

end CFSG.KBRoute.XGRuP12t

end
