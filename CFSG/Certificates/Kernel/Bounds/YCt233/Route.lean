module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vData
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.YCt233

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)],
    [(1, true), (1, true)],
    [(2, true), (2, true)],
    [(3, true), (3, true)],
    [(4, true), (4, true)],
    [(5, true), (5, true)],
    [(6, true), (6, true)],
    [(7, true), (7, true)],
    [(8, true), (8, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(0, true), (2, true), (0, true), (2, true)],
    [(0, true), (3, true), (0, true), (3, true), (0, true), (3, true)],
    [(0, true), (4, true), (0, true), (4, true)],
    [(0, true), (5, true), (0, true), (5, true)],
    [(0, true), (6, true), (0, true), (6, true), (0, true), (6, true)],
    [(0, true), (7, true), (0, true), (7, true)],
    [(0, true), (8, true), (0, true), (8, true)],
    [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)],
    [(1, true), (3, true), (1, true), (3, true)],
    [(1, true), (4, true), (1, true), (4, true)],
    [(1, true), (5, true), (1, true), (5, true)],
    [(1, true), (6, true), (1, true), (6, true)],
    [(1, true), (7, true), (1, true), (7, true)],
    [(1, true), (8, true), (1, true), (8, true)],
    [(2, true), (3, true), (2, true), (3, true)],
    [(2, true), (4, true), (2, true), (4, true)],
    [(2, true), (5, true), (2, true), (5, true)],
    [(2, true), (6, true), (2, true), (6, true)],
    [(2, true), (7, true), (2, true), (7, true)],
    [(2, true), (8, true), (2, true), (8, true)],
    [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)],
    [(3, true), (5, true), (3, true), (5, true)],
    [(3, true), (6, true), (3, true), (6, true)],
    [(3, true), (7, true), (3, true), (7, true)],
    [(3, true), (8, true), (3, true), (8, true)],
    [(4, true), (5, true), (4, true), (5, true), (4, true), (5, true)],
    [(4, true), (6, true), (4, true), (6, true)],
    [(4, true), (7, true), (4, true), (7, true)],
    [(4, true), (8, true), (4, true), (8, true)],
    [(5, true), (6, true), (5, true), (6, true)],
    [(5, true), (7, true), (5, true), (7, true)],
    [(5, true), (8, true), (5, true), (8, true)],
    [(6, true), (7, true), (6, true), (7, true), (6, true), (7, true)],
    [(6, true), (8, true), (6, true), (8, true)],
    [(7, true), (8, true), (7, true), (8, true), (7, true), (8, true)],
    [(0, true), (1, true), (2, true), (0, true), (3, true), (4, true), (0, true), (6, true), (7, true), (0, true), (1, true), (2, true), (0, true), (3, true), (4, true), (0, true), (6, true), (7, true), (0, true), (1, true), (2, true), (0, true), (3, true), (4, true), (0, true), (6, true), (7, true), (0, true), (1, true), (2, true), (0, true), (3, true), (4, true), (0, true), (6, true), (7, true), (0, true), (1, true), (2, true), (0, true), (3, true), (4, true), (0, true), (6, true), (7, true), (0, true), (1, true), (2, true), (0, true), (3, true), (4, true), (0, true), (6, true), (7, true), (0, true), (1, true), (2, true), (0, true), (3, true), (4, true), (0, true), (6, true), (7, true), (0, true), (1, true), (2, true), (0, true), (3, true), (4, true), (0, true), (6, true), (7, true), (0, true), (1, true), (2, true), (0, true), (3, true), (4, true), (0, true), (6, true), (7, true), (0, true), (1, true), (2, true), (0, true), (3, true), (4, true), (0, true), (6, true), (7, true)]]

#kb_table CFSG.KBRoute.YCt233 T1 YCt233_T1v include_bytes "data/YCt233_T1v.meta" 843515 12715723446149309956 166599134359138271745 CFSG.KBRoute.YCt233.rels "1 2 4 5 6 7 8 9"

theorem top : KB.topOk T1.amap (nat_lit 9) = true := by quickRfl

end CFSG.KBRoute.YCt233

end
