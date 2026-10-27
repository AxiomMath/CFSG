module

public import CFSG.Certificates.Kernel.McL.Sub
public import CFSG.Certificates.Kernel.McL.Model
public import CFSG.Certificates.Kernel.McL.Dce
public import CFSG.Certificates.Kernel.McL.Rels
public import CFSG.Certificates.Kernel.McL.TC
public import CFSG.Certificates.Kernel.McL.Data.A1
public import CFSG.Certificates.Kernel.McL.Data.A2
public import CFSG.Certificates.Kernel.McL.Data.A3
public import CFSG.Certificates.Kernel.McL.Data.A4
public import CFSG.Certificates.Kernel.McL.Data.A5
public import CFSG.Certificates.Kernel.McL.Data.AM
public import CFSG.Certificates.Kernel.McL.Data.AS
public import CFSG.Certificates.Kernel.McL.Data.AI
public import CFSG.Certificates.Kernel.McL.Data.BM
public import CFSG.Certificates.Kernel.McL.Data.BI
public import CFSG.Certificates.Kernel.McL.Data.BR
public import CFSG.Certificates.Kernel.McL.Data.CQ
public import CFSG.Certificates.Kernel.McL.Data.CN
public import CFSG.Certificates.Kernel.McL.Data.D
public import CFSG.Certificates.Kernel.McL.Data.M
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.McL.Bind

theorem xt : CFSG.KC.McL.Sub.xtOK CFSG.KC.McL.Rels.XT = true := by
  quickRfl

theorem qA1 : Nat.beq (CFSG.KC.McL.Sub.bindRun CFSG.KC.McL.Rels.XT CFSG.KC.McL.Rels.QR
    CFSG.KD.McL.A1.TW CFSG.KD.McL.A1.TL (nat_lit 78) CFSG.KD.McL.A1.nT (CFSG.KC.McL.pid
    CFSG.KD.McL.A1.d) (CFSG.KC.McL.pid CFSG.KD.McL.A1.d) (nat_lit 14)
    (nat_lit 0x24a000049000348000447000546000208000107000006000205000104000003000502000401000300)
    (nat_lit 1)) (nat_lit 0xf8000000000000003ff) = true := by
  quickRfl

theorem qA2 : Nat.beq (CFSG.KC.McL.Sub.bindRun CFSG.KC.McL.Rels.XT CFSG.KC.McL.Rels.QR
    CFSG.KD.McL.A2.TW CFSG.KD.McL.A2.TL (nat_lit 78) CFSG.KD.McL.A2.nT (CFSG.KC.McL.pid
    CFSG.KD.McL.A2.d) (CFSG.KC.McL.pid CFSG.KD.McL.A2.d) (nat_lit 3) (nat_lit 165788766852612171)
    (nat_lit 1)) (nat_lit 0x70000000000000000001) = true := by
  quickRfl

theorem qA3 : Nat.beq (CFSG.KC.McL.Sub.bindRun CFSG.KC.McL.Rels.XT CFSG.KC.McL.Rels.QR
    CFSG.KD.McL.A3.TW CFSG.KD.McL.A3.TL (nat_lit 78) CFSG.KD.McL.A3.nT (CFSG.KC.McL.pid
    CFSG.KD.McL.A3.d) (CFSG.KC.McL.pid CFSG.KD.McL.A3.d) (nat_lit 19)
    (nat_lit 0x121b00111a001019000f18000e17000d16000c15000b14000a1300091200081100071000060f00050e00040d00030c00020b00010a000009)
    (nat_lit 1)) (nat_lit 536869889) = true := by
  quickRfl

theorem qA4 : Nat.beq (CFSG.KC.McL.Sub.bindRun CFSG.KC.McL.Rels.XT CFSG.KC.McL.Rels.QR
    CFSG.KD.McL.A4.TW CFSG.KD.McL.A4.TL (nat_lit 78) CFSG.KD.McL.A4.nT (CFSG.KC.McL.pid
    CFSG.KD.McL.A4.d) (CFSG.KC.McL.pid CFSG.KD.McL.A4.d) (nat_lit 13)
    (nat_lit 0x838000736000232000331000c2c000b2500062400042300012200092100002000051e000a1c)
    (nat_lit 1)) (nat_lit 183557413037670401) = true := by
  quickRfl

theorem qA5 : Nat.beq (CFSG.KC.McL.Sub.bindRun CFSG.KC.McL.Rels.XT CFSG.KC.McL.Rels.QR
    CFSG.KD.McL.A5.TW CFSG.KD.McL.A5.TL (nat_lit 78) CFSG.KD.McL.A5.nT (CFSG.KC.McL.pid
    CFSG.KD.McL.A5.d) (CFSG.KC.McL.pid CFSG.KD.McL.A5.d) (nat_lit 29)
    (nat_lit 0x1c45001b44001743000d42001541001940000e3f00103e000f3d00163c00073b000c3a00123900033700013500133400083300143000042f000b2e00052d001a2b00182a000229001128000a2700092600061f00001d)
    (nat_lit 1)) (nat_lit 0x7ffd73df8140000001) = true := by
  quickRfl

theorem qAll : Nat.beq (Nat.lor (Nat.lor (Nat.lor (Nat.lor (nat_lit 0x7c000000000000001ff)
    (nat_lit 0x38000000000000000000)) (nat_lit 268434944)) (nat_lit 91778706518835200))
    (nat_lit 0x3ffeb9efc0a0000000)) (nat_lit 0x3fffffffffffffffffff) = true := by
  quickRfl

theorem gAI : Nat.beq (CFSG.KC.McL.Sub.bindRun CFSG.KC.McL.Rels.XD CFSG.KC.McL.Rels.GR
    CFSG.KD.McL.AI.TW CFSG.KD.McL.AI.TL (nat_lit 34) CFSG.KD.McL.AI.nT (CFSG.KC.McL.pid
    CFSG.KD.McL.AI.d) (CFSG.KC.McL.pid CFSG.KD.McL.AI.d) (nat_lit 15)
    (nat_lit 0xe1e000d1c000c1b000b1a000a1900091800081700071500061400051300041200031100021000010f00000e)
    (nat_lit 1)) (nat_lit 3212804097) = true := by
  quickRfl

theorem gAS : Nat.beq (CFSG.KC.McL.Sub.bindRun CFSG.KC.McL.Rels.XD CFSG.KC.McL.Rels.GR
    CFSG.KD.McL.AS.TW CFSG.KD.McL.AS.TL (nat_lit 34) CFSG.KD.McL.AS.nT (CFSG.KC.McL.pid
    CFSG.KD.McL.AS.d) (CFSG.KC.McL.pid CFSG.KD.McL.AS.d) (nat_lit 14)
    (nat_lit 0x92100082000071f00031d00010d00020c00000b000607000506000405000304000203000102000001)
    (nat_lit 1)) (nat_lit 31138542077) = true := by
  quickRfl

theorem gBI : Nat.beq (CFSG.KC.McL.Sub.bindRun CFSG.KC.McL.Rels.XD CFSG.KC.McL.Rels.GR
    CFSG.KD.McL.BI.TW CFSG.KD.McL.BI.TL (nat_lit 34) CFSG.KD.McL.BI.nT (CFSG.KC.McL.pid
    CFSG.KD.McL.BI.d) (CFSG.KC.McL.evalW CFSG.KC.McL.Rels.MG (nat_lit 44) (CFSG.KC.LceS.wWord
    CFSG.KC.McL.Rels.K1W) (CFSG.KC.LceS.wLen CFSG.KC.McL.Rels.K1W)) (nat_lit 1) (nat_lit 22)
    (nat_lit 1)) (nat_lit 8388609) = true := by
  quickRfl

theorem gBM : Nat.beq (CFSG.KC.McL.Sub.bindRun CFSG.KC.McL.Rels.XD CFSG.KC.McL.Rels.GR
    CFSG.KD.McL.BM.TW CFSG.KD.McL.BM.TL (nat_lit 34) CFSG.KD.McL.BM.nT (CFSG.KC.McL.pid
    CFSG.KD.McL.BM.d) (CFSG.KC.McL.evalW CFSG.KC.McL.Rels.MG (nat_lit 44) (CFSG.KC.LceS.wWord
    CFSG.KC.McL.Rels.K1W) (CFSG.KC.LceS.wLen CFSG.KC.McL.Rels.K1W)) (nat_lit 3)
    (nat_lit 146929942288924680) (nat_lit 1)) (nat_lit 3585) = true := by
  quickRfl

theorem g0 : CFSG.KC.McL.Sub.conjRelOK CFSG.KC.McL.TC.sel (nat_lit 15) (nat_lit 0) (nat_lit 1)
    (CFSG.KC.McL.Sub.subst CFSG.KC.McL.Rels.XD (CFSG.KC.McL.Sub.ofEnt (CFSG.KC.McL.Rels.GR
    (nat_lit 0)))) = true := by
  quickRfl

theorem gAll : Nat.beq (Nat.lor (Nat.lor (Nat.lor (Nat.lor (nat_lit 1) (nat_lit 1606402048))
    (nat_lit 15569271038)) (nat_lit 4194304)) (nat_lit 1792)) (nat_lit 17179869183) = true := by
  quickRfl

theorem k1 : CFSG.KC.McL.Sub.k1Run CFSG.KC.McL.Rels.XT CFSG.KC.McL.Rels.MG CFSG.KD.McL.BR.TW
    CFSG.KD.McL.BR.TL CFSG.KC.McL.Rels.KS CFSG.KC.McL.Rels.KQ CFSG.KC.McL.Rels.KH (nat_lit 44)
    CFSG.KD.McL.BR.nT (nat_lit 3) (CFSG.KC.McL.evalW CFSG.KC.McL.Rels.MG (nat_lit 44)
    (CFSG.KC.LceS.wWord CFSG.KC.McL.Rels.K1W) (CFSG.KC.LceS.wLen CFSG.KC.McL.Rels.K1W)) = true := by
  quickRfl

theorem sBM : CFSG.KC.McL.Sub.subsOK CFSG.KC.McL.Rels.XT CFSG.KC.McL.Rels.MG CFSG.KD.McL.BM.ST
    CFSG.KD.McL.BM.SL CFSG.KD.McL.BM.SN CFSG.KD.McL.BM.SH CFSG.KD.McL.AM.TW CFSG.KD.McL.AM.TL
    (nat_lit 44) CFSG.KD.McL.AM.nT (CFSG.KC.McL.pid CFSG.KD.McL.AM.d) CFSG.KD.McL.BM.K = true := by
  quickRfl

theorem dBM : Nat.beq CFSG.KD.McL.BM.d (nat_lit 44) = true := by
  quickRfl

theorem sBI : CFSG.KC.McL.Sub.subsOK CFSG.KC.McL.Rels.XT CFSG.KC.McL.Rels.MG CFSG.KD.McL.BI.ST
    CFSG.KD.McL.BI.SL CFSG.KD.McL.BI.SN CFSG.KD.McL.BI.SH CFSG.KD.McL.AM.TW CFSG.KD.McL.AM.TL
    (nat_lit 44) CFSG.KD.McL.AM.nT (CFSG.KC.McL.pid CFSG.KD.McL.AM.d) CFSG.KD.McL.BI.K = true := by
  quickRfl

theorem dBI : Nat.beq CFSG.KD.McL.BI.d (nat_lit 44) = true := by
  quickRfl

theorem sBR : CFSG.KC.McL.Sub.subsOK CFSG.KC.McL.Rels.XT CFSG.KC.McL.Rels.MG CFSG.KD.McL.BR.ST
    CFSG.KD.McL.BR.SL CFSG.KD.McL.BR.SN CFSG.KD.McL.BR.SH CFSG.KD.McL.AM.TW CFSG.KD.McL.AM.TL
    (nat_lit 44) CFSG.KD.McL.AM.nT (CFSG.KC.McL.pid CFSG.KD.McL.AM.d) CFSG.KD.McL.BR.K = true := by
  quickRfl

theorem dBR : Nat.beq CFSG.KD.McL.BR.d (nat_lit 44) = true := by
  quickRfl

theorem mGens : CFSG.KC.McL.Sub.gensOK CFSG.KC.McL.Rels.MG (nat_lit 44) (nat_lit 3) = true := by
  quickRfl

theorem mRels : CFSG.KC.McL.Sub.relsHold CFSG.KC.McL.Rels.MG CFSG.KC.McL.Rels.QR (nat_lit 44)
    (nat_lit 78) = true := by
  quickRfl

theorem pQ : CFSG.KC.McL.Sub.evenLens CFSG.KC.McL.Rels.QR (nat_lit 78) = true := by
  quickRfl

theorem pK : CFSG.KC.McL.Sub.evenLens CFSG.KC.McL.Rels.NR1 (nat_lit 79) = true := by
  quickRfl

theorem pG : CFSG.KC.McL.Sub.evenLens CFSG.KC.McL.Rels.GR (nat_lit 34) = true := by
  quickRfl

theorem p5 : Nat.beq (CFSG.KC.McL.Rels.QR (nat_lit 3)) CFSG.KC.McL.Rels.P5 = true := by
  quickRfl

theorem p5n : Nat.beq (CFSG.KC.McL.Rels.NR1 (nat_lit 3)) CFSG.KC.McL.Rels.P5 = true := by
  quickRfl

theorem mOrd : Nat.beq (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (nat_lit 1)
    (CFSG.KC.McL.Model.orbCount (CFSG.KC.McL.Model.orbitRun CFSG.KD.McL.M.EP CFSG.KD.McL.M.ED
    CFSG.KD.McL.M.BP (nat_lit 0) (nat_lit 13) CFSG.KD.McL.M.OJ0))) (CFSG.KC.McL.Model.orbCount
    (CFSG.KC.McL.Model.orbitRun CFSG.KD.McL.M.EP CFSG.KD.McL.M.ED CFSG.KD.McL.M.BP (nat_lit 1)
    (nat_lit 5) CFSG.KD.McL.M.OJ1))) (CFSG.KC.McL.Model.orbCount (CFSG.KC.McL.Model.orbitRun
    CFSG.KD.McL.M.EP CFSG.KD.McL.M.ED CFSG.KD.McL.M.BP (nat_lit 2) (nat_lit 4) CFSG.KD.McL.M.OJ2)))
    (CFSG.KC.McL.Model.orbCount (CFSG.KC.McL.Model.orbitRun CFSG.KD.McL.M.EP CFSG.KD.McL.M.ED
    CFSG.KD.McL.M.BP (nat_lit 3) (nat_lit 3) CFSG.KD.McL.M.OJ3))) (CFSG.KC.McL.Model.orbCount
    (CFSG.KC.McL.Model.orbitRun CFSG.KD.McL.M.EP CFSG.KD.McL.M.ED CFSG.KD.McL.M.BP (nat_lit 4)
    (nat_lit 2) CFSG.KD.McL.M.OJ4))) (CFSG.KC.McL.Model.orbCount (CFSG.KC.McL.Model.orbitRun
    CFSG.KD.McL.M.EP CFSG.KD.McL.M.ED CFSG.KD.McL.M.BP (nat_lit 5) (nat_lit 1) CFSG.KD.McL.M.OJ5)))
    (CFSG.KC.McL.Model.orbCount (CFSG.KC.McL.Model.orbitRun CFSG.KD.McL.M.EP CFSG.KD.McL.M.ED
    CFSG.KD.McL.M.BP (nat_lit 6) (nat_lit 15) CFSG.KD.McL.M.OJ6))) (nat_lit 161280) = true := by
  quickRfl

theorem mLev : Nat.beq CFSG.KD.McL.M.nLev (nat_lit 7) = true := by
  quickRfl

theorem cQ : Nat.beq (Nat.mul (nat_lit 5) CFSG.KD.McL.CQ.nAlive) (nat_lit 161280) = true := by
  quickRfl

theorem cN : Nat.beq (Nat.mul (nat_lit 5) CFSG.KD.McL.CN.nAlive) CFSG.KD.McL.D.NORD = true := by
  quickRfl

theorem fin : Nat.beq (Nat.div (Nat.mul CFSG.KD.McL.D.NORD CFSG.KD.McL.D.SUM) (nat_lit 2))
    (nat_lit 898128000) = true := by
  quickRfl

theorem fin2 : Nat.beq (Nat.mod (Nat.mul CFSG.KD.McL.D.NORD CFSG.KD.McL.D.SUM) (nat_lit 2))
    (nat_lit 0) = true := by
  quickRfl

theorem trw0 : CFSG.KC.McL.Dce.membWordOK CFSG.KD.McL.D.TRW0 (nat_lit 1) = true := by
  quickRfl

theorem trw1 : CFSG.KC.McL.Dce.membWordOK CFSG.KD.McL.D.TRW1 (nat_lit 2) = true := by
  quickRfl

end CFSG.KD.McL.Bind

end
