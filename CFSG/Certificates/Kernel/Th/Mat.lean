module

public section

namespace CFSG.KC.Th

@[expose] def c0 : Nat := nat_lit 14742041600653298778164464186675034565339440968075561999656263336489234065757151420561541415618923938782311094303562262231923774852187994847031891473161258761755557889
@[expose] def rowMask : Nat := nat_lit 16777215
@[expose] def ident24 : Nat := nat_lit 123665204422062557356803572788677631011309541569709136179232403901906511584503046599112559797157752258954946564622144514457573459535397137501359353526631510665794982588186625
@[expose] def m1lo : Nat := nat_lit 4095
@[expose] def m1hi : Nat := nat_lit 16773120
@[expose] def m2lo : Nat := nat_lit 31331363893816558455789081633249712926328737500232906198749230544269048311789602658582591
@[expose] def m2hi : Nat := nat_lit 2005207289204259741170501224527981627285039200014905996719950754833219091954534570149285824
@[expose] def m3lo : Nat := nat_lit 77634751435382816068195597156006343696220241591785518973279923344885133646303398148312495057566319984336782909063687637475447013383
@[expose] def m3hi : Nat := nat_lit 621078011483062528545564777248050749569761932734284151786239386759081069170427185186499960460530559874694263272509501099803576107064
@[expose] def m4a : Nat := nat_lit 52374249726338269920222125828018069694904588741968191740379635527817564034522288814292816431204049121484472467000179395471715146806010973164294207700993
@[expose] def m4b : Nat := nat_lit 104748499452676539840444251656036139389809177483936383480759271055635128069044577628585632862408098242968944934000358790943430293612021946328588415401986
@[expose] def m4c : Nat := nat_lit 209496998905353079680888503312072278779618354967872766961518542111270256138089155257171265724816196485937889868000717581886860587224043892657176830803972

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def mstep (c rm A B acc k ks : Nat) : Nat :=
  Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) c) rm)
    (Nat.mul (Nat.land (Nat.shiftRight B ks) rm) c))

@[expose] noncomputable def mulStep (A B acc k k24 : Nat) : Nat :=
  Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) c0) rowMask)
    (Nat.mul (Nat.land (Nat.shiftRight B k24) rowMask) c0))

@[expose] noncomputable def mul24 (A B : Nat) : Nat :=
  mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (nat_lit 0) (nat_lit 0) (nat_lit 0)) (nat_lit 1) (nat_lit 24)) (nat_lit 2) (nat_lit 48)) (nat_lit 3) (nat_lit 72)) (nat_lit 4) (nat_lit 96)) (nat_lit 5) (nat_lit 120)) (nat_lit 6) (nat_lit 144)) (nat_lit 7) (nat_lit 168)) (nat_lit 8) (nat_lit 192)) (nat_lit 9) (nat_lit 216)) (nat_lit 10) (nat_lit 240)) (nat_lit 11) (nat_lit 264)) (nat_lit 12) (nat_lit 288)) (nat_lit 13) (nat_lit 312)) (nat_lit 14) (nat_lit 336)) (nat_lit 15) (nat_lit 360)) (nat_lit 16) (nat_lit 384)) (nat_lit 17) (nat_lit 408)) (nat_lit 18) (nat_lit 432)) (nat_lit 19) (nat_lit 456)) (nat_lit 20) (nat_lit 480)) (nat_lit 21) (nat_lit 504)) (nat_lit 22) (nat_lit 528)) (nat_lit 23) (nat_lit 552)

@[expose] noncomputable def mulRows (c X B : Nat) : Nat :=
  mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (mstep c rowMask X B (nat_lit 0) (nat_lit 0) (nat_lit 0)) (nat_lit 1) (nat_lit 24)) (nat_lit 2) (nat_lit 48)) (nat_lit 3) (nat_lit 72)) (nat_lit 4) (nat_lit 96)) (nat_lit 5) (nat_lit 120)) (nat_lit 6) (nat_lit 144)) (nat_lit 7) (nat_lit 168)) (nat_lit 8) (nat_lit 192)) (nat_lit 9) (nat_lit 216)) (nat_lit 10) (nat_lit 240)) (nat_lit 11) (nat_lit 264)) (nat_lit 12) (nat_lit 288)) (nat_lit 13) (nat_lit 312)) (nat_lit 14) (nat_lit 336)) (nat_lit 15) (nat_lit 360)) (nat_lit 16) (nat_lit 384)) (nat_lit 17) (nat_lit 408)) (nat_lit 18) (nat_lit 432)) (nat_lit 19) (nat_lit 456)) (nat_lit 20) (nat_lit 480)) (nat_lit 21) (nat_lit 504)) (nat_lit 22) (nat_lit 528)) (nat_lit 23) (nat_lit 552)

@[expose] noncomputable def sp1 (x : Nat) : Nat := Nat.lor (Nat.land x m1lo) (Nat.shiftLeft (Nat.land x m1hi) (nat_lit 276))
@[expose] noncomputable def sp2 (x : Nat) : Nat := Nat.lor (Nat.land x m2lo) (Nat.shiftLeft (Nat.land x m2hi) (nat_lit 138))
@[expose] noncomputable def sp3 (x : Nat) : Nat := Nat.lor (Nat.land x m3lo) (Nat.shiftLeft (Nat.land x m3hi) (nat_lit 69))
@[expose] noncomputable def sp4 (x : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land x m4a) (Nat.shiftLeft (Nat.land x m4b) (nat_lit 23))) (Nat.shiftLeft (Nat.land x m4c) (nat_lit 46))
@[expose] noncomputable def spreadS (x : Nat) : Nat := Nat.mul (sp4 (sp3 (sp2 (sp1 x)))) rowMask
@[expose] noncomputable def fold1 (t : Nat) : Nat := Nat.xor t (Nat.shiftRight t (nat_lit 288))
@[expose] noncomputable def fold2 (t : Nat) : Nat := Nat.xor t (Nat.shiftRight t (nat_lit 144))
@[expose] noncomputable def fold3 (t : Nat) : Nat := Nat.xor t (Nat.shiftRight t (nat_lit 72))
@[expose] noncomputable def fold45 (t : Nat) : Nat :=
  Nat.xor t (Nat.xor (Nat.shiftRight t (nat_lit 24)) (Nat.shiftRight t (nat_lit 48)))

@[expose] noncomputable def vecmul (x M : Nat) : Nat :=
  Nat.land (fold45 (fold3 (fold2 (fold1 (Nat.land (spreadS x) M))))) rowMask

@[expose] noncomputable def chkMul (C A B : Nat) : Bool := Nat.beq C (mul24 A B)
@[expose] noncomputable def chkInv (A B : Nat) : Bool := Nat.beq (mul24 A B) ident24
@[expose] noncomputable def chkVec (w v M : Nat) : Bool := Nat.beq w (vecmul v M)
@[expose] noncomputable def chkLt (a b : Nat) : Bool := Nat.blt a b
@[expose] noncomputable def chkEq (a b : Nat) : Bool := Nat.beq a b

@[expose] noncomputable def permRows (X tau n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight X
      (Nat.mul (nat_lit 24) (Nat.land (Nat.shiftRight tau (Nat.mul (nat_lit 7) i)) (nat_lit 127)))) rowMask) (Nat.mul (nat_lit 24) i))) n

@[expose] noncomputable def rowOf (P i : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 24) i)) rowMask

@[expose] noncomputable def rowsOK (n P : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) (rowOf P (nat_lit 0)))
    (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => andB acc (Nat.blt (rowOf P i) (rowOf P (Nat.succ i)))) (Nat.sub n (nat_lit 1)))

@[expose] noncomputable def chkAct (c n P M Q tau : Nat) : Bool := Nat.beq (permRows (mulRows c P M) tau n) Q

end CFSG.KC.Th

end
