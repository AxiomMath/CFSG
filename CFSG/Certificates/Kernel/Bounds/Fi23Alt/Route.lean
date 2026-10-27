module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Fi23.T1vData
public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T2vData
public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T3vData
public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T4vData
public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T5vData
public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T6vData
public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T7vData
public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T8vData
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Fi23Alt

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)], [(3, true), (3, true)], [(4, true), (4, true)], [(5, true), (5, true)], [(6, true), (6, true)], [(7, true), (7, true)], [(8, true), (8, true)], [(9, true), (9, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)], [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true)], [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)], [(4, true), (5, true), (4, true), (5, true), (4, true), (5, true)], [(5, true), (6, true), (5, true), (6, true), (5, true), (6, true)], [(6, true), (9, true), (6, true), (9, true), (6, true), (9, true)], [(3, true), (7, true), (3, true), (7, true), (3, true), (7, true)], [(7, true), (8, true), (7, true), (8, true), (7, true), (8, true)], [(0, true), (2, true), (0, true), (2, true)], [(0, true), (3, true), (0, true), (3, true)], [(0, true), (4, true), (0, true), (4, true)], [(0, true), (5, true), (0, true), (5, true)], [(0, true), (6, true), (0, true), (6, true)], [(0, true), (7, true), (0, true), (7, true)], [(0, true), (8, true), (0, true), (8, true)], [(0, true), (9, true), (0, true), (9, true)], [(1, true), (3, true), (1, true), (3, true)], [(1, true), (4, true), (1, true), (4, true)], [(1, true), (5, true), (1, true), (5, true)], [(1, true), (6, true), (1, true), (6, true)], [(1, true), (7, true), (1, true), (7, true)], [(1, true), (8, true), (1, true), (8, true)], [(1, true), (9, true), (1, true), (9, true)], [(2, true), (4, true), (2, true), (4, true)], [(2, true), (5, true), (2, true), (5, true)], [(2, true), (6, true), (2, true), (6, true)], [(2, true), (7, true), (2, true), (7, true)], [(2, true), (8, true), (2, true), (8, true)], [(2, true), (9, true), (2, true), (9, true)], [(3, true), (5, true), (3, true), (5, true)], [(3, true), (6, true), (3, true), (6, true)], [(3, true), (8, true), (3, true), (8, true)], [(3, true), (9, true), (3, true), (9, true)], [(4, true), (6, true), (4, true), (6, true)], [(4, true), (7, true), (4, true), (7, true)], [(4, true), (8, true), (4, true), (8, true)], [(4, true), (9, true), (4, true), (9, true)], [(5, true), (7, true), (5, true), (7, true)], [(5, true), (8, true), (5, true), (8, true)], [(5, true), (9, true), (5, true), (9, true)], [(6, true), (7, true), (6, true), (7, true)], [(6, true), (8, true), (6, true), (8, true)], [(7, true), (9, true), (7, true), (9, true)], [(8, true), (9, true), (8, true), (9, true)], [(3, true), (2, true), (1, true), (3, true), (4, true), (5, true), (3, true), (7, true), (8, true), (3, true), (2, true), (1, true), (3, true), (4, true), (5, true), (3, true), (7, true), (8, true), (3, true), (2, true), (1, true), (3, true), (4, true), (5, true), (3, true), (7, true), (8, true), (3, true), (2, true), (1, true), (3, true), (4, true), (5, true), (3, true), (7, true), (8, true), (3, true), (2, true), (1, true), (3, true), (4, true), (5, true), (3, true), (7, true), (8, true), (3, true), (2, true), (1, true), (3, true), (4, true), (5, true), (3, true), (7, true), (8, true), (3, true), (2, true), (1, true), (3, true), (4, true), (5, true), (3, true), (7, true), (8, true), (3, true), (2, true), (1, true), (3, true), (4, true), (5, true), (3, true), (7, true), (8, true), (3, true), (2, true), (1, true), (3, true), (4, true), (5, true), (3, true), (7, true), (8, true), (3, true), (2, true), (1, true), (3, true), (4, true), (5, true), (3, true), (7, true), (8, true)], [(0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (7, true), (0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (7, true), (0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (7, true), (0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (7, true), (0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (7, true), (0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (7, true), (0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (7, true), (0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (7, true), (0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (7, true)]]

#kb_table CFSG.KBRoute.Fi23Alt T1 Fi23_T1v include_bytes "../Fi23/data/Fi23_T1v.meta" 48104 3369080862903338071 47390263963055590408705 CFSG.KBRoute.Fi23Alt.rels "1 2 3 4 5 6 7 8 9"

#kb_table CFSG.KBRoute.Fi23Alt T2 Fi23Alt_T2v include_bytes "data/Fi23Alt_T2v.meta" 17952 12982892168782353700 166599134359138271745 CFSG.KBRoute.Fi23Alt.rels "2 3 4 5 6 7 8 9"

#kb_table CFSG.KBRoute.Fi23Alt T3 Fi23Alt_T3v include_bytes "data/Fi23Alt_T3v.meta" 5889 3637198685387493052 148080050112590643456 CFSG.KBRoute.Fi23Alt.rels "2 3 4 5 6 7 8"

#kb_table CFSG.KBRoute.Fi23Alt T4 Fi23Alt_T4v include_bytes "data/Fi23Alt_T4v.meta" 234 9308773109518189731 506097522914230528 CFSG.KBRoute.Fi23Alt.rels "2 3 4 5 6 8"

#kb_table CFSG.KBRoute.Fi23Alt T5 Fi23Alt_T5v include_bytes "data/Fi23Alt_T5v.meta" 197 18176214870019121049 432351079016038656 CFSG.KBRoute.Fi23Alt.rels "3 4 5 6 8"

#kb_table CFSG.KBRoute.Fi23Alt T6 Fi23Alt_T6v include_bytes "data/Fi23Alt_T6v.meta" 174 9669619943384468520 360292381154672640 CFSG.KBRoute.Fi23Alt.rels "3 4 5 8"

#kb_table CFSG.KBRoute.Fi23Alt T7 Fi23Alt_T7v include_bytes "data/Fi23Alt_T7v.meta" 162 506152847281273565 288230389070233600 CFSG.KBRoute.Fi23Alt.rels "4 5 8"

#kb_table CFSG.KBRoute.Fi23Alt T8 Fi23Alt_T8v include_bytes "data/Fi23Alt_T8v.meta" 167 18355108117141339478 216172790720495616 CFSG.KBRoute.Fi23Alt.rels ""

theorem top : KB.topOk T1.amap (nat_lit 10) = true := by quickRfl

theorem link_T1 : KB.linkOk T2.amap T1.words = true := by quickRfl

theorem link_T2 : KB.linkOk T3.amap T2.words = true := by quickRfl

theorem link_T3 : KB.linkOk T4.amap T3.words = true := by quickRfl

theorem link_T4 : KB.linkOk T5.amap T4.words = true := by quickRfl

theorem link_T5 : KB.linkOk T6.amap T5.words = true := by quickRfl

theorem link_T6 : KB.linkOk T7.amap T6.words = true := by quickRfl

theorem link_T7 : KB.linkOk T8.amap T7.words = true := by quickRfl

theorem order_from_T2 : Nat.beq (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul T2.N T3.N) T4.N) T5.N) T6.N) T7.N) T8.N) (nat_lit 129123503308800) = true := by quickRfl

theorem order_from_T3 : Nat.beq (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul T3.N T4.N) T5.N) T6.N) T7.N) T8.N) (nat_lit 9170703360) = true := by quickRfl

theorem order_from_T4 : Nat.beq (Nat.mul (Nat.mul (Nat.mul (Nat.mul T4.N T5.N) T6.N) T7.N) T8.N) (nat_lit 2903040) = true := by quickRfl

theorem order_from_T5 : Nat.beq (Nat.mul (Nat.mul (Nat.mul T5.N T6.N) T7.N) T8.N) (nat_lit 51840) = true := by quickRfl

theorem order_from_T6 : Nat.beq (Nat.mul (Nat.mul T6.N T7.N) T8.N) (nat_lit 1920) = true := by quickRfl

theorem order_from_T7 : Nat.beq (Nat.mul T7.N T8.N) (nat_lit 192) = true := by quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul T1.N T2.N) T3.N) T4.N) T5.N) T6.N) T7.N) T8.N) (nat_lit 4089470473293004800) = true := by quickRfl

end CFSG.KBRoute.Fi23Alt

end
