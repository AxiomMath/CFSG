module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.McL.Rels
public import CFSG.Certificates.Kernel.McL.Data.CQ
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.McL.CQ

theorem sH0 : CFSG.KC.LceS.wordsOK selWT CFSG.KC.McL.Rels.QR CFSG.KC.McL.Rels.STQ INV INV8
    (nat_lit 2048) HS = true := by quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 6) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 159) nC nAlive = true := by quickRfl

end CFSG.KD.McL.CQ

end
