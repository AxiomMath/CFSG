module

public import CFSG.Certificates.Kernel.BabyMonster.F2

public section

namespace CFSG.KC.BM

@[expose] noncomputable def mulSG4 (S : Nat) (Bs : List Nat) (A0 A1 A2 A3 : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool) (fun c0 c1 c2 c3 => k c0 c1 c2 c3)
    (fun u ih c0 c1 c2 c3 =>
      (fun t SMa SMb =>
        List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
            Nat → Nat → Bool)
          (fun _ _ _ _ x0 y0 x1 y1 x2 y2 x3 y3 =>
            forceBB (Nat.xor c0 (Nat.xor (Nat.shiftRight x0 t) (Nat.shiftRight y0 (Nat.succ t))))
              (fun c0 => forceBB
              (Nat.xor c1 (Nat.xor (Nat.shiftRight x1 t) (Nat.shiftRight y1 (Nat.succ t))))
              (fun c1 => forceBB
              (Nat.xor c2 (Nat.xor (Nat.shiftRight x2 t) (Nat.shiftRight y2 (Nat.succ t))))
              (fun c2 => forceBB
              (Nat.xor c3 (Nat.xor (Nat.shiftRight x3 t) (Nat.shiftRight y3 (Nat.succ t))))
              (fun c3 => ih c0 c1 c2 c3)))))
          (fun T _ ih2 E0 E1 E2 E3 x0 y0 x1 y1 x2 y2 x3 y3 =>
            (fun Ra Rb => ih2 (Nat.shiftRight E0 (nat_lit 4096)) (Nat.shiftRight E1 (nat_lit 4096))
                (Nat.shiftRight E2 (nat_lit 4096)) (Nat.shiftRight E3 (nat_lit 4096))
                (Nat.xor x0 (Nat.mul (Nat.land E0 LM) Ra))
                (Nat.xor y0 (Nat.mul (Nat.shiftRight
                  (Nat.land E0 (nat_lit 340282366920938463463374607431768211455)) (nat_lit 64)) Rb))
                (Nat.xor x1 (Nat.mul (Nat.land E1 LM) Ra))
                (Nat.xor y1 (Nat.mul (Nat.shiftRight
                  (Nat.land E1 (nat_lit 340282366920938463463374607431768211455)) (nat_lit 64)) Rb))
                (Nat.xor x2 (Nat.mul (Nat.land E2 LM) Ra))
                (Nat.xor y2 (Nat.mul (Nat.shiftRight
                  (Nat.land E2 (nat_lit 340282366920938463463374607431768211455)) (nat_lit 64)) Rb))
                (Nat.xor x3 (Nat.mul (Nat.land E3 LM) Ra))
                (Nat.xor y3 (Nat.mul (Nat.shiftRight
                  (Nat.land E3 (nat_lit 340282366920938463463374607431768211455)) (nat_lit 64)) Rb)))
              (Nat.land T SMa) (Nat.land T SMb))
          Bs (Nat.shiftRight A0 (Nat.mul (nat_lit 64) t)) (Nat.shiftRight A1 (Nat.mul (nat_lit 64) t))
          (Nat.shiftRight A2 (Nat.mul (nat_lit 64) t)) (Nat.shiftRight A3 (Nat.mul (nat_lit 64) t))
          (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)
          (nat_lit 0))
        (Nat.add u u) (Nat.shiftLeft S (Nat.add u u)) (Nat.shiftLeft S (Nat.succ (Nat.add u u))))
    (nat_lit 32) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def mulS4 (Bs : List Nat) (A0 A1 A2 A3 : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) : Bool :=
  mulSG4 SM Bs A0 A1 A2 A3 k

@[expose] noncomputable def mulW4 (Ws : List (List Nat)) (A0 A1 A2 A3 : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool) k
    (fun Bs _ ih a0 a1 a2 a3 => mulS4 Bs a0 a1 a2 a3 ih) Ws A0 A1 A2 A3

@[expose] noncomputable def beq4 (c0 c1 c2 c3 d0 d1 d2 d3 : Nat) : Bool :=
  andB (andB (Nat.beq c0 d0) (Nat.beq c1 d1)) (andB (Nat.beq c2 d2) (Nat.beq c3 d3))

@[expose] noncomputable def rhs4 (Ds : List (List Nat)) (C0 C1 C2 C3 : Nat) :
    Nat → Nat → Nat → Nat → Bool :=
  fun c0 c1 c2 c3 => mulW4 Ds C0 C1 C2 C3 (beq4 c0 c1 c2 c3)

@[expose] noncomputable def LMB : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)) (nat_lit 1)

@[expose] noncomputable def mulR4 (Rb : List (List Nat)) (A0 A1 A2 A3 : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ _ _ _ c0 c1 c2 c3 => k c0 c1 c2 c3)
    (fun blk _ ih E0 E1 E2 E3 c0 c1 c2 c3 =>
      List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
        (fun _ _ _ _ c0 c1 c2 c3 => forceBB c0 (fun c0 => forceBB c1 (fun c1 =>
          forceBB c2 (fun c2 => forceBB c3 (fun c3 =>
          ih (Nat.shiftRight E0 (nat_lit 4096)) (Nat.shiftRight E1 (nat_lit 4096))
            (Nat.shiftRight E2 (nat_lit 4096)) (Nat.shiftRight E3 (nat_lit 4096)) c0 c1 c2 c3)))))
        (fun R _ ih2 B0 B1 B2 B3 c0 c1 c2 c3 => ih2 (Nat.shiftRight B0 (nat_lit 64))
          (Nat.shiftRight B1 (nat_lit 64)) (Nat.shiftRight B2 (nat_lit 64))
          (Nat.shiftRight B3 (nat_lit 64))
          (Nat.xor c0 (Nat.mul (Nat.land B0 LM) R)) (Nat.xor c1 (Nat.mul (Nat.land B1 LM) R))
          (Nat.xor c2 (Nat.mul (Nat.land B2 LM) R)) (Nat.xor c3 (Nat.mul (Nat.land B3 LM) R)))
        blk (Nat.land E0 LMB) (Nat.land E1 LMB) (Nat.land E2 LMB) (Nat.land E3 LMB) c0 c1 c2 c3)
    Rb A0 A1 A2 A3 (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def spreadBlkOK (T : Nat) (blk : List Nat) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat → Nat) (fun t => t)
    (fun R _ ih t => Bool.rec (motive := fun _ => Nat) (nat_lit 100000) (ih (Nat.succ t))
      (Nat.beq R (Nat.land (Nat.shiftRight T t) SM))) blk (nat_lit 0)) (nat_lit 64)

@[expose] noncomputable def spreadOK (Rb : List (List Nat)) (Bs : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun Bs => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Bs)
    (fun blk _ ih Bs => List.rec (motive := fun _ => Bool) false
      (fun T Ts _ => andB (spreadBlkOK T blk) (ih Ts)) Bs) Rb Bs

end CFSG.KC.BM

end
