module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Enum

@[expose] noncomputable def zPowOK (n w m nw z : Nat) (Z Zi : Nat → Nat) (nZ : Nat) : Bool :=
  bAnd(allN n (fun p => Nat.beq (pg w m (Z (nat_lit 0)) p) p),
    allN nZ (fun e => bAnd(permOK n w m nw (Z e) (Zi e),
      bIf(Nat.blt (Nat.succ e) nZ, eq2 n w m (Z (Nat.succ e)) (Z e) z, true))))

@[expose] noncomputable def zChk (T : Nat → Nat) (sh lm rb rm n w m nw pm iw im nL : Nat)
    (Z Zi : Nat → Nat) (nZ i : Nat) : Bool :=
  strictB (rget T sh lm rb rm i) (fun r =>
  strictB (Nat.land r pm) (fun x =>
  strictB (Nat.add nw (Nat.add iw iw)) (fun o =>
  strictB fld(r, o, nat_lit 15) (fun e =>
  strictB fld(r, Nat.add o (nat_lit 4), im) (fun j =>
  strictB fld(r, Nat.add o (Nat.add iw (nat_lit 4)), im) (fun p =>
    bAnd(Nat.blt (nat_lit 0) e, bAnd(Nat.blt e nZ, bAnd(Nat.blt j nL, bAnd(Nat.blt p n,
      strictB (rperm T sh lm rb rm pm j) (fun v =>
        bAnd(eq3 n w m v (Z e) x (Zi e),
          bIf(Nat.beq (pg w m x (pg w m v p)) (pg w m v (pg w m x p)), false, true)))))))))))))

@[expose] noncomputable def zRange (T : Nat → Nat) (sh lm rb rm n w m nw pm iw im nL : Nat)
    (Z Zi : Nat → Nat) (nZ lo cnt : Nat) : Bool :=
  allN cnt (fun k => zChk T sh lm rb rm n w m nw pm iw im nL Z Zi nZ (Nat.add lo k))

end CFSG.KC.Enum

end
