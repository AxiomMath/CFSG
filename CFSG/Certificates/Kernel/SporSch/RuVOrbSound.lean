module

public import Certificates.Data.Kernel.VecK
public import Certificates.Data.CFSGNative.HS.Cert
import CFSG.Certificates.Kernel.SporSch.RuVOrbProved

public section

namespace CFSG.KC.VecK

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native

theorem vOrbit_tables (D : VecData) {csA csB : List Char} {MA MB NA NB : Nat}
    {P AT BT FO S IP SP : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true) :
    ∀ i < D.n, ap (D.orbit ()).alpha i = lk AT (nat_lit 32) i ∧
      ap (D.orbit ()).beta i = lk BT (nat_lit 32) i :=
  vOrbit_tables_proved D hA hB hseed hn hP0 horb hbfs hsort

end CFSG.KC.VecK

end
