module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.HN.T3vData
public import CFSG.Certificates.Kernel.Bounds.HN.T4vData
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Rels
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Const
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KC.HNA.N5A

#kb_table CFSG.KC.HNA.N5A T3 HN_T3v include_bytes "../HN/data/HN_T3v.meta" 208 6188853611543198152 197121 CFSG.KC.HNA.rels "1 2"

#kb_table CFSG.KC.HNA.N5A T4 HN_T4v include_bytes "../HN/data/HN_T4v.meta" 3754 6849299384866482994 513 CFSG.KC.HNA.rels ""

theorem top : KB.topOk T3.amap (nat_lit 3) = true := by quickRfl

theorem link_T3 : KB.linkOk T4.amap T3.words = true := by quickRfl

@[expose] def tOrd : Nat := (nat_lit 5)

theorem t_pow : KB.powOk (KB.idAmap (nat_lit 5)) [[(4, true)]] tOrd CFSG.KC.HNA.rels = true := by quickRfl

theorem t_conj_a : KB.relIn (KB.idAmap (nat_lit 5)) [(0, false), (4, true), (0, true), (4, true), (4, true)] CFSG.KC.HNA.rels = true := by quickRfl

theorem t_conj_c : KB.relIn (KB.idAmap (nat_lit 5)) [(2, false), (4, true), (2, true), (4, false), (4, false)] CFSG.KC.HNA.rels = true := by quickRfl

theorem t_conj_b : KB.relIn (KB.idAmap (nat_lit 5)) [(4, false), (1, false), (4, true), (1, true)] CFSG.KC.HNA.rels = true := by quickRfl

theorem nord : Nat.beq CFSG.KD.HNA.NORD (Nat.mul (Nat.mul tOrd T3.N) T4.N) = true := by quickRfl

end CFSG.KC.HNA.N5A

end
