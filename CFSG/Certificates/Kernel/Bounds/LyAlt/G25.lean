module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Ly.T2vData
public import CFSG.Certificates.Kernel.Bounds.Ly.T3vData
public import CFSG.Certificates.Kernel.Bounds.Ly.T4vData
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Rels
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Const
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KC.LyA.G25

#kb_table CFSG.KC.LyA.G25 T2 Ly_T2v include_bytes "../Ly/data/Ly_T2v.meta" 3356 3989419925565358272 21542142465 CFSG.KC.LyA.rels "1 2 3"

#kb_table CFSG.KC.LyA.G25 T3 Ly_T3v include_bytes "../Ly/data/Ly_T3v.meta" 2015 10471031543470858090 197121 CFSG.KC.LyA.rels "1 2"

#kb_table CFSG.KC.LyA.G25 T4 Ly_T4v include_bytes "../Ly/data/Ly_T4v.meta" 316 13380513186314871098 513 CFSG.KC.LyA.rels ""

theorem top : KB.topOk T2.amap (nat_lit 5) = true := by quickRfl

theorem link_T2 : KB.linkOk T3.amap T2.words = true := by quickRfl

theorem link_T3 : KB.linkOk T4.amap T3.words = true := by quickRfl

theorem nord : Nat.beq CFSG.KD.LyA.NORD (Nat.mul (Nat.mul T2.N T3.N) T4.N) = true := by quickRfl

end CFSG.KC.LyA.G25

end
