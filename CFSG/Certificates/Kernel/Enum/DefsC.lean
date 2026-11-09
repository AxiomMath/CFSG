module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Enum

@[expose] noncomputable def rdC (w m p j : Nat) : Nat :=
  strictN (Nat.shiftRight j (nat_lit 4)) (fun c =>
    fld(fld(p, Nat.mul (Nat.mul w (nat_lit 16)) c,
        Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w (nat_lit 16))) (nat_lit 1)),
      Nat.mul w (Nat.land j (nat_lit 15)), m))

@[expose] noncomputable def leafC (w m p q lo : Nat) : Nat :=
  strictN fld(q, Nat.mul w lo, Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w (nat_lit 8))) (nat_lit 1))
    (fun Q => Nat.lor
      (Nat.lor
        (Nat.lor (rdC w m p fld(Q, Nat.mul w (nat_lit 0), m))
          (Nat.shiftLeft (rdC w m p fld(Q, Nat.mul w (nat_lit 1), m)) w))
        (Nat.shiftLeft
          (Nat.lor (rdC w m p fld(Q, Nat.mul w (nat_lit 2), m))
            (Nat.shiftLeft (rdC w m p fld(Q, Nat.mul w (nat_lit 3), m)) w))
          (Nat.mul w (nat_lit 2))))
      (Nat.shiftLeft
        (Nat.lor
          (Nat.lor (rdC w m p fld(Q, Nat.mul w (nat_lit 4), m))
            (Nat.shiftLeft (rdC w m p fld(Q, Nat.mul w (nat_lit 5), m)) w))
          (Nat.shiftLeft
            (Nat.lor (rdC w m p fld(Q, Nat.mul w (nat_lit 6), m))
              (Nat.shiftLeft (rdC w m p fld(Q, Nat.mul w (nat_lit 7), m)) w))
            (Nat.mul w (nat_lit 2))))
        (Nat.mul w (nat_lit 4))))

@[expose] noncomputable def pmkC (w m p q : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun lo => leafC w m p q lo)
    (fun d ih lo => Nat.lor (ih lo)
      (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft (nat_lit 8) d))) (Nat.mul w (Nat.shiftLeft (nat_lit 8) d))))

@[expose] noncomputable def pcompC (n w m p q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih b rem => nIf(Nat.beq rem (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0), ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)),
        strictN (Nat.sub n (Nat.shiftLeft rem b)) (fun lo =>
          Nat.lor (Nat.shiftLeft (nIf(Nat.blt b (nat_lit 3), pmkH w m p q b lo, pmkC w m p q (Nat.sub b (nat_lit 3)) lo))
              (Nat.mul w lo))
            (ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)))))))
    (nat_lit 32) (nat_lit 0) n

end CFSG.KC.Enum

end
