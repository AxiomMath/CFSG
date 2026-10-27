module

public import CFSG.Certificates.Kernel.McL.Perm
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.McL.Model

open CFSG.KC CFSG.KC.Loop CFSG.KC.McL

@[expose] noncomputable def dKind (D : Nat) : Nat := Nat.land D (nat_lit 3)
@[expose] noncomputable def dA (D : Nat) : Nat := Nat.land (Nat.shiftRight D (nat_lit 4)) (nat_lit 4095)
@[expose] noncomputable def dB (D : Nat) : Nat := Nat.land (Nat.shiftRight D (nat_lit 16)) (nat_lit 4095)
@[expose] noncomputable def dL (D : Nat) : Nat := Nat.shiftRight D (nat_lit 28)

@[expose] noncomputable def bpt (BP l : Nat) : Nat := Nat.land (Nat.shiftRight BP (Nat.mul (nat_lit 6) l)) (nat_lit 63)

@[expose] noncomputable def entOK (G EP ED : Nat → Nat) (d g BP e : Nat) : Bool :=
  (fun D P => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (andB (Nat.blt (dA D) e) (andB (Nat.ble (nat_lit 1) (dL D))
            (andB (Nat.ble (Nat.sub (dL D) (nat_lit 1)) (dL (ED (dA D))))
              (andB (Nat.beq P (EP (dA D)))
                (Nat.beq (pget P (bpt BP (Nat.sub (dL D) (nat_lit 1)))) (bpt BP (Nat.sub (dL D) (nat_lit 1))))))))
          (Nat.beq (dKind D) (nat_lit 3)))
        (andB (Nat.blt (dA D) e) (andB (Nat.ble (dL D) (dL (ED (dA D))))
          (andB (inRange d P) (andB (Nat.beq (Nat.shiftRight P (Nat.mul (nat_lit 6) d)) (nat_lit 0))
            (Nat.beq (pmul d P (EP (dA D))) (pid d))))))
        (Nat.beq (dKind D) (nat_lit 2)))
      (andB (Nat.blt (dA D) e) (andB (Nat.blt (dB D) e)
        (andB (Nat.ble (dL D) (dL (ED (dA D)))) (andB (Nat.ble (dL D) (dL (ED (dB D))))
          (Nat.beq P (pmul d (EP (dA D)) (EP (dB D))))))))
      (Nat.beq (dKind D) (nat_lit 1)))
    (andB (Nat.blt (dA D) (Nat.mul (nat_lit 2) g)) (andB (Nat.beq (dL D) (nat_lit 0)) (Nat.beq P (G (dA D)))))
    (Nat.beq (dKind D) (nat_lit 0)))
  (ED e) (EP e)

@[expose] noncomputable def elemsOK (G EP ED : Nat → Nat) (d g BP m : Nat) : Bool :=
  Loop.allBelow m (Nat.add (Nat.shiftRight m (nat_lit 6)) (nat_lit 1)) (fun e => entOK G EP ED d g BP e)

@[expose] noncomputable def orbitRun (EP ED : Nat → Nat) (BP l m J : Nat) : Nat :=
  (fun res => Nat.land res (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 72)) (nat_lit 1)))
  (Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ S => S)
    (fun _ ih J S => (fun cnt seen pts par gen => (fun p => ih (Nat.shiftRight J (nat_lit 18))
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (Nat.lor (Nat.succ cnt) (Nat.lor (Nat.shiftLeft (Nat.lor seen (Nat.shiftLeft (nat_lit 1) p)) (nat_lit 8))
            (Nat.shiftLeft (Nat.lor pts (Nat.shiftLeft p (Nat.mul (nat_lit 6) cnt))) (nat_lit 72))))
          (andB (Nat.blt (nat_lit 0) cnt) (andB (Nat.blt par cnt) (andB (Nat.blt (nat_lit 0) (EP gen))
            (andB (Nat.ble l (dL (ED gen)))
            (Nat.beq (Nat.land seen (Nat.shiftLeft (nat_lit 1) p)) (nat_lit 0))))))))
        (pget (EP gen) (pget pts par)))
      (Nat.land S (nat_lit 255)) (Nat.land (Nat.shiftRight S (nat_lit 8)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 64)) (nat_lit 1)))
      (Nat.shiftRight S (nat_lit 72)) (Nat.land J (nat_lit 63)) (Nat.land (Nat.shiftRight J (nat_lit 6)) (nat_lit 4095)))
    m J
    (Nat.lor (nat_lit 1) (Nat.lor (Nat.shiftLeft (Nat.shiftLeft (nat_lit 1) (bpt BP l)) (nat_lit 8))
      (Nat.shiftLeft (bpt BP l) (nat_lit 72)))))

@[expose] noncomputable def orbCount (S : Nat) : Nat := Nat.land S (nat_lit 255)

end CFSG.KC.McL.Model

end
