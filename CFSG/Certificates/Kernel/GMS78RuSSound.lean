module

public import Certificates.Data.Kernel.GMS78RuSClo
public import CFSG.Certificates.Kernel.GMS78RuPSound
import CFSG.Certificates.Kernel.GMS78RuSM.Check16
import CFSG.Certificates.Kernel.GMS78RuS17.Main

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

theorem check16_sound (gA : Array (Fin 8)) (dA : Array (Nat × Fin 8)) (dct : List Lin8) (ε : Bool)
    (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO : Nat) (INVL KEYL : List Nat)
    (hT : sTabs gA dA dct ε GT DPR LIN DM DO)
    (hI : INVL = sInvs (mul16K GT DPR LIN DM DO) 2048)
    (hK : ∀ i < INVL.length, Nat.beq (sKey (mul16K GT DPR LIN DM DO) 2048 (INVL.getD i 0))
      (kKeyPart (KEYL.getD i 0)) = true)
    (hF : kFin16 (mul16K GT DPR LIN DM DO) INVL KEYL = true) :
    Gen.check16G gA dA dct ε = true := by
  exact SM.check16_sound gA dA dct ε GT DPR LIN DM DO INVL KEYL hT hI hK hF

theorem check17_sound (gA : Array (Fin 8)) (dA : Array (Nat × Fin 8)) (dct : List Lin8) (ε : Bool)
    (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO : Nat) (INVL KEYL : List Nat)
    (hT : sTabs gA dA dct ε GT DPR LIN DM DO)
    (hI : INVL = sInvs (mul17K GT DPR LIN DM DO) 8192)
    (hK : ∀ i < INVL.length, kKey17 (mul17K GT DPR LIN DM DO) (INVL.getD i 0) (KEYL.getD i 0) = true)
    (hC : ∀ i < INVL.length, kClo17 (mul17K GT DPR LIN DM DO) (INVL.getD i 0) (KEYL.getD i 0) = true)
    (hF : kFin17 (mul17K GT DPR LIN DM DO) inX17 INVL KEYL = true) :
    Gen.check17G gA dA dct ε = true := by
  exact S17.check17_of gA dA dct ε GT DPR LIN DM DO INVL KEYL hT
    (fun _ hp _ hq => SM.mul17K_eq hT hp hq) (SM.mul17G_lt hT) hI hK hC hF

end CFSG.KC.GMS

end
