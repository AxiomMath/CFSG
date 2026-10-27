module

public import CFSG.Certificates.Kernel.J2OrbProof

public section

namespace CFSG.KC.J2Orb

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.J1.Native

theorem orbBFS_sound {p d cap N : Nat} {A B : List (List Nat)} {root : List Nat}
    {PTP ALP BEP : Nat} (h : orbK p d cap N A B root PTP ALP BEP = true) :
    (orbBFS p id A B root cap).alpha =
        Array.ofFn (n := N) (fun i => UInt32.ofNat (pg 9 511 ALP i.val)) ∧
      (orbBFS p id A B root cap).beta =
        Array.ofFn (n := N) (fun i => UInt32.ofNat (pg 9 511 BEP i.val)) :=
  orbBFS_sound_proved h

end CFSG.KC.J2Orb

end
