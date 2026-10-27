module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Enum

@[expose] noncomputable def cIdx (T : Nat → Nat) (sh lm rb rm nw iw im W len i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun i => i)
    (fun k ih i => strictN fld(rget T sh lm rb rm i,
      nIf(Nat.beq (wl W k) (nat_lit 0), nw, Nat.add nw iw), im) ih) len i

@[expose] noncomputable def cPow (T : Nat → Nat) (sh lm rb rm nw iw im W len e i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun i => i)
    (fun _ ih i => strictN (cIdx T sh lm rb rm nw iw im W len i) ih) e i

@[expose] noncomputable def zChkI (T : Nat → Nat) (sh lm rb rm n w m nw pm iw im W len nE i : Nat) :
    Bool :=
  strictB (rget T sh lm rb rm i) (fun r =>
  strictB (Nat.land r pm) (fun x =>
  strictB fld(r, Nat.add nw (Nat.add iw iw), nat_lit 15) (fun e =>
  strictB fld(r, Nat.add nw (Nat.add (Nat.add iw iw) (Nat.add iw (nat_lit 4))), im) (fun p =>
    bAnd(Nat.blt (nat_lit 0) e, bAnd(Nat.blt e nE, bAnd(Nat.blt p n,
      strictB (rperm T sh lm rb rm pm (cPow T sh lm rb rm nw iw im W len e i)) (fun v =>
        bIf(Nat.beq (pg w m x (pg w m v p)) (pg w m v (pg w m x p)), false, true)))))))))

@[expose] noncomputable def zRangeI (T : Nat → Nat) (sh lm rb rm n w m nw pm iw im W len nE lo cnt :
    Nat) : Bool :=
  allN cnt (fun k => zChkI T sh lm rb rm n w m nw pm iw im W len nE (Nat.add lo k))

end CFSG.KC.Enum

end
