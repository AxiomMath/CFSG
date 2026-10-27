module

public import CFSG.Certificates.Kernel.J4.M24Rs
public import CFSG.Certificates.Kernel.J4.M24Data.M24R
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyFour
import CFSG.Certificates.Kernel.Common.Harness
import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.KBAlt.M24

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)], [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]]

theorem rels_eq : TauCeti.Sporadic.m24Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.m24Presentation_transcribed]
  simp [FreeGroup.invRev, rels]

@[expose] noncomputable def letCode (p : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat)
    (fun g b => Bool.rec (motive := fun _ => Nat) (Nat.succ (Nat.mul (nat_lit 2) g))
      (Nat.mul (nat_lit 2) g) b) p

@[expose] noncomputable def encW (w : List (Nat × Bool)) : Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun x _ ih => Prod.rec (motive := fun _ => Nat × Nat)
      (fun v n => Prod.mk (Nat.lor (letCode x) (Nat.shiftLeft v (nat_lit 16))) (Nat.succ n)) ih) w

@[expose] noncomputable def encRel (w : List (Nat × Bool)) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun v n => CFSG.KM24.pk v n) (encW w)

@[expose] noncomputable def encRels (L : List (List (Nat × Bool))) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun h _ ih => List.cons (encRel h) ih) L

theorem r0_bind : CFSG.KM24.eqRL CFSG.KD.M24R.R0 (encRels rels) = true := by quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul (nat_lit 24) (nat_lit 443520)) (nat_lit 23))
    (nat_lit 244823040) = true := by quickRfl

end CFSG.KBAlt.M24

end
