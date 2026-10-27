module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Co3.T1vData
public import CFSG.Certificates.Kernel.Bounds.Co3Alt.T2vData
public import CFSG.Certificates.Kernel.Bounds.Co3Alt.T3vData
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Co3Alt

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)], [(3, true), (3, true)], [(4, true), (4, true)], [(5, true), (5, true)], [(6, true), (6, true)], [(0, true), (2, true), (0, true), (2, true)], [(0, true), (3, true), (0, true), (3, true)], [(0, true), (4, true), (0, true), (4, true)], [(1, true), (3, true), (1, true), (3, true)], [(2, true), (4, true), (2, true), (4, true)], [(3, true), (6, true), (3, true), (6, true)], [(4, true), (6, true), (4, true), (6, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true)], [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)], [(5, true), (0, true), (6, true), (0, true), (6, true), (0, true), (6, true)], [(6, true), (1, true), (5, true), (1, true), (5, true), (1, true), (5, true)], [(2, true), (5, true), (6, true), (2, true), (5, true), (6, true), (2, true), (5, true), (6, true)], [(4, true), (0, true), (1, true), (2, true), (0, true), (1, true), (2, true), (0, true), (1, true), (2, true)], [(4, true), (0, true), (2, true), (6, true), (0, true), (2, true), (6, true), (0, true), (2, true), (6, true), (0, true), (2, true), (6, true)], [(1, true), (2, true), (5, true), (2, true), (5, true), (1, true), (2, true), (5, true), (2, true), (5, true), (1, true), (2, true), (5, true), (2, true), (5, true)], [(4, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true)]]

#kb_table CFSG.KBRoute.Co3Alt T1 Co3_T1v include_bytes "../Co3/data/Co3_T1v.meta" 444782 11767286554750447795 1976943448883713 CFSG.KBRoute.Co3Alt.rels "1 2 3 5 6 7"

#kb_table CFSG.KBRoute.Co3Alt T2 Co3Alt_T2v include_bytes "data/Co3Alt_T2v.meta" 8300 12552019413653892842 1694364598469121 CFSG.KBRoute.Co3Alt.rels "1 3 5 6 7"

#kb_table CFSG.KBRoute.Co3Alt T3 Co3Alt_T3v include_bytes "data/Co3Alt_T3v.meta" 508 12915761034985254573 1411785815097345 CFSG.KBRoute.Co3Alt.rels ""

theorem top : KB.topOk T1.amap (nat_lit 7) = true := by quickRfl

theorem link_T1 : KB.linkOk T2.amap T1.words = true := by quickRfl

theorem link_T2 : KB.linkOk T3.amap T2.words = true := by quickRfl

theorem order_from_T2 : Nat.beq (Nat.mul T2.N T3.N) (nat_lit 2903040) = true := by quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul T1.N T2.N) T3.N) (nat_lit 495766656000) = true := by quickRfl

end CFSG.KBRoute.Co3Alt

end
