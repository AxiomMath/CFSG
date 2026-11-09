module

public import CFSG.Certificates.Kernel.Common.LabZ

public section

namespace CFSG.KC.LabM

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop CFSG.KC.LabF CFSG.KC.LabZ

@[expose] noncomputable def readsM (MB : Nat → Nat) (ft n : Nat) (k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k ih R => Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (nat_lit 0) (MB (Nat.shiftRight (Nat.land R 4294967295) (nat_lit 1))))
        (ih (Nat.shiftRight R (nat_lit 32))))
      (ih R)
      (Nat.beq (Nat.sub n (Nat.succ k)) ft)) k

@[expose] noncomputable def labStepM (LB MB : Nat → Nat) (Hs J S w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (Nat.beq (LB (Nat.sub S (nat_lit 1))) (nat_lit 0)))
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (labWalk LB (Nat.sub S (nat_lit 1)) J w
                (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535))))
              (readsM MB (Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)) (wLen w)
                (wLen w) (Nat.shiftRight J (nat_lit 53)))))
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (labWalk LB (Nat.sub S (nat_lit 1)) J w
              (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))))
          (Nat.beq (MB (Nat.sub S (nat_lit 1))) (nat_lit 2)))
        (Nat.succ S)
        (Nat.beq (MB (Nat.sub S (nat_lit 1))) (nat_lit 0)))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.blt (nat_lit 0) S)

@[expose] noncomputable def labChunkM (WT LB MB : Nat → Nat) (Hs C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (strictN (labStepM LB MB Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        strictN (labStepM LB MB Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runLabM (WT LB MB : Nat → Nat) (Hs : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (labChunkM WT LB MB Hs C S) ih) Cs

@[expose] noncomputable def labStepZM (CD MB : Nat → Nat) (Hs J S w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (Nat.beq (Nat.land (CD (Nat.sub S (nat_lit 1))) (nat_lit 15)) (nat_lit 0)))
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (labWalkZ CD (Nat.sub S (nat_lit 1)) J w
                (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535))))
              (readsM MB (Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)) (wLen w)
                (wLen w) (Nat.shiftRight J (nat_lit 53)))))
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (labWalkZ CD (Nat.sub S (nat_lit 1)) J w
              (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))))
          (Nat.beq (MB (Nat.sub S (nat_lit 1))) (nat_lit 2)))
        (Nat.succ S)
        (Nat.beq (MB (Nat.sub S (nat_lit 1))) (nat_lit 0)))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.blt (nat_lit 0) S)

@[expose] noncomputable def labChunkZM (WT CD MB : Nat → Nat) (Hs C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (strictN (labStepZM CD MB Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        strictN (labStepZM CD MB Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runLabCM (WT CD MB : Nat → Nat) (Hs : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (labChunkZM WT CD MB Hs C S) ih) Cs

theorem runLabM_append (WT LB MB : Nat → Nat) (Hs : Nat) : ∀ (l1 l2 : List Nat) (x : Nat),
    runLabM WT LB MB Hs (List.append l1 l2) x = runLabM WT LB MB Hs l2 (runLabM WT LB MB Hs l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (labChunkM WT LB MB Hs C x) (runLabM WT LB MB Hs (List.append l1 l2)) =
      runLabM WT LB MB Hs l2 (strictN (labChunkM WT LB MB Hs C x) (runLabM WT LB MB Hs l1))
    rw [strictN_eq, strictN_eq]
    exact runLabM_append WT LB MB Hs l1 l2 _

section Run

variable {LB CD : Nat → Nat} (hLB : ∀ i, LB i = pwN (pcode (CD i)))

include hLB

theorem labStepM_eq (MB : Nat → Nat) : labStepM LB MB = labStepZM CD MB := by
  funext Hs J S w
  unfold labStepM labStepZM
  rw [hLB, pwN_code_zero, labWalk_eq hLB]

theorem runLabM_eq (WT MB : Nat → Nat) (Hs : Nat) : runLabM WT LB MB Hs = runLabCM WT CD MB Hs := by
  funext Cs S
  unfold runLabM runLabCM labChunkM labChunkZM
  rw [labStepM_eq hLB]

end Run

end CFSG.KC.LabM

end
