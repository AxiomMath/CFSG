module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.ON.T1vData
public import CFSG.Certificates.Kernel.Bounds.ON.T2vData
public import CFSG.Certificates.Kernel.Bounds.ON.T3vData
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.ON

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)], [(3, true), (3, true)], [(4, true), (4, true)], [(5, true), (5, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)], [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)], [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)], [(4, true), (5, true), (4, true), (5, true), (4, true), (5, true)], [(0, true), (2, true), (0, true), (2, true)], [(0, true), (3, true), (0, true), (3, true)], [(0, true), (4, true), (0, true), (4, true)], [(0, true), (5, true), (0, true), (5, true)], [(1, true), (3, true), (1, true), (3, true)], [(1, true), (4, true), (1, true), (4, true)], [(1, true), (5, true), (1, true), (5, true)], [(2, true), (4, true), (2, true), (4, true)], [(2, true), (5, true), (2, true), (5, true)], [(3, true), (5, true), (3, true), (5, true)], [(6, true), (6, true), (6, true), (6, true)], [(5, false), (0, false), (6, true), (6, true)], [(5, false), (0, false), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)], [(2, true), (6, false), (3, false), (6, false), (3, false), (2, true), (3, true), (6, true), (3, true), (6, true)], [(3, true), (6, false), (2, false), (6, false), (2, false), (3, true), (2, true), (6, true), (2, true), (6, true)], [(1, true), (2, true), (3, true), (6, true), (1, true), (2, true), (3, true), (6, true), (1, true), (2, true), (3, true), (6, true), (1, true), (2, true), (3, true), (6, true), (1, true), (2, true), (3, true), (6, true)], [(6, true), (1, true), (2, false), (6, true), (2, true), (1, false), (6, true), (1, true), (2, false), (6, true), (2, true)], [(6, true), (4, true), (3, false), (6, true), (3, true), (4, false), (6, true), (4, true), (3, false), (6, true), (3, true)]]

#kb_table CFSG.KBRoute.ON T1 ON_T1v include_bytes "data/ON_T1v.meta" 150458 8368350981384399335 1976943448883713 CFSG.KBRoute.ON.rels "1 2 3 4 5 6"

#kb_table CFSG.KBRoute.ON T2 ON_T2v include_bytes "data/ON_T2v.meta" 21395 5071441041055874478 6618611909121 CFSG.KBRoute.ON.rels "1 2 3 5 6"

#kb_table CFSG.KBRoute.ON T3 ON_T3v include_bytes "data/ON_T3v.meta" 275 17620954660328610475 5514738205185 CFSG.KBRoute.ON.rels ""

theorem top : KB.topOk T1.amap (nat_lit 7) = true := by quickRfl

theorem link_T1 : KB.linkOk T2.amap T1.words = true := by quickRfl

theorem link_T2 : KB.linkOk T3.amap T2.words = true := by quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul T1.N T2.N) T3.N) (nat_lit 460815505920) = true := by quickRfl

end CFSG.KBRoute.ON

end
