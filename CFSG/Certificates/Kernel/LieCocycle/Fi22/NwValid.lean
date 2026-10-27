module

public import CFSG.Certificates.Kernel.LieCocycle.Fi22.Search

public section

namespace CFSG.KLC.Fi22

@[expose] noncomputable def nwValid (NW : Nat) : Bool :=
  andB (Nat.blt NW (Nat.shiftLeft (nat_lit 1) (nat_lit 94208)))
    (Nat.rec (motive := fun _ => Bool) true
      (fun s ih => andB ih ((fun m d => andB (Nat.beq (Nat.land m (Nat.shiftLeft m d)) (nat_lit 0))
          (Nat.beq (Nat.shiftRight m (Nat.sub (nat_lit 4096) d)) (nat_lit 0)))
        (nwMask NW s) (stageDist s)))
      (nat_lit 23))

@[expose] noncomputable def nwsValid (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun NW _ ih => andB (nwValid NW) ih) L

@[expose] noncomputable def presOkV (GA NW MB n : Nat) : Bool := andB (nwValid NW) (presOk GA NW MB n)

@[expose] noncomputable def leafOkV (n MB TA NWs NWk ACC : Nat) : Bool :=
  andB (andB (nwValid NWs) (nwValid NWk)) (leafOk n MB TA NWs NWk ACC)

end CFSG.KLC.Fi22

end
