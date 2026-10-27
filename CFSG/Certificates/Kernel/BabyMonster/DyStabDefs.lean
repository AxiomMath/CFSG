module

public import CFSG.Certificates.Kernel.BabyMonster.BenesAlign
public import CFSG.Certificates.Kernel.BabyMonster.PktDecode
public import CFSG.Certificates.Kernel.MonsterConv.PermValid

public section

namespace CFSG.KC.BM.Dy

open CFSG.KC.BM CFSG.KC.BM.Lat CFSG.KC.BM.Pkt

@[expose] noncomputable def rowsNe (C : List (List Nat)) (X : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih (andB (Nat.blt (recOf C i) dyFail) (notB (Nat.beq (recOf C i) X))))

@[expose] noncomputable def stagesOK (Ms Ds : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun M _ ih Ds => List.rec (motive := fun _ => Bool) true
      (fun D Ds' _ => andB (CFSG.KC.MonsterConv.Perm.dswValid (nat_lit 131072) D M) (ih Ds')) Ds)
    Ms Ds

@[expose] noncomputable def netV (Ms : List Nat) (T : Nat) : Bool :=
  andB (stagesOK Ms dyDs) (tabOK T)

end CFSG.KC.BM.Dy

end
