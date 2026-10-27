module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.M23.T1vData
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.M23

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)], [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)], [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false)], [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true)]]

#kb_table CFSG.KBRoute.M23 T1 M23_T1v include_bytes "data/M23_T1v.meta" 179167 12051786777623850778 513 CFSG.KBRoute.M23.rels "1,2"

theorem top : KB.topOk T1.amap (nat_lit 2) = true := by quickRfl

@[expose] def bottom : Nat := (nat_lit 23)

theorem power : KB.powOk T1.amap T1.words bottom rels = true := by quickRfl

theorem order : Nat.beq (Nat.mul T1.N bottom) (nat_lit 10200960) = true := by quickRfl

end CFSG.KBRoute.M23

end
