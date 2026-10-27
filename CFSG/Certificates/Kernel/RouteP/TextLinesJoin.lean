module

public import CFSG.Certificates.Kernel.RouteP.TextLines
public import Certificates.Data.Kernel.RouteP.TextLinesJoin
public import CFSG.Certificates.Kernel.Common.ListSlices
import Mathlib.Tactic.SplitIfs

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.RouteP CFSG.KS.ListSlices

section Join

variable (E : Nat → Nat → Nat) (lens : Nat → Nat)

theorem nlChk_nil (L P num iN cm sa : Nat) (fin : Nat → Nat → Nat → Nat → Nat → Nat → Bool) :
    nlChk E lens [] L P num iN cm sa fin = fin L P num iN cm sa := rfl

theorem nlChk_append (a b : List Nat) : ∀ (L P num iN cm sa : Nat)
    (fin : Nat → Nat → Nat → Nat → Nat → Nat → Bool),
    nlChk E lens (a ++ b) L P num iN cm sa fin =
      nlChk E lens a L P num iN cm sa fun L P num iN cm sa => nlChk E lens b L P num iN cm sa fin := by
  induction a with
  | nil => intros; rfl
  | cons n a ih =>
    intro L P num iN cm sa fin
    rw [List.cons_append]
    simp only [nlChk_cons, ih]

theorem nlChk_mono (fin fin' : Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (hf : ∀ L P num iN cm sa, fin L P num iN cm sa = true → fin' L P num iN cm sa = true) :
    ∀ (ns : List Nat) (L P num iN cm sa : Nat),
      nlChk E lens ns L P num iN cm sa fin = true → nlChk E lens ns L P num iN cm sa fin' = true
  | [], L, P, num, iN, cm, sa, h => hf L P num iN cm sa h
  | n :: ns, L, P, num, iN, cm, sa, h => by
    revert h
    rw [nlChk_cons, nlChk_cons]
    simp only [bif'_eq, forceN_eq]
    split_ifs <;>
      first
        | exact fun h => h
        | exact nlChk_mono fin fin' hf ns _ _ _ _ _ _

theorem nlAt_eq {L' P' num' iN' cm' sa' L P num iN cm sa : Nat}
    (h : nlAt L' P' num' iN' cm' sa' L P num iN cm sa = true) :
    L = L' ∧ P = P' ∧ num = num' ∧ iN = iN' ∧ cm = cm' ∧ sa = sa' := by
  simpa only [nlAt, Bool.and_eq_true, Nat.beq_eq] using h

theorem nlChk_append_at {a b : List Nat} {L P num iN cm sa L' P' num' iN' cm' sa' : Nat}
    {fin : Nat → Nat → Nat → Nat → Nat → Nat → Bool}
    (h1 : nlChk E lens a L P num iN cm sa (nlAt L' P' num' iN' cm' sa') = true)
    (h2 : nlChk E lens b L' P' num' iN' cm' sa' fin = true) :
    nlChk E lens (a ++ b) L P num iN cm sa fin = true := by
  rw [nlChk_append]
  refine nlChk_mono E lens _ _ ?_ a _ _ _ _ _ _ h1
  intro L P num iN cm sa h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := nlAt_eq h
  exact h2

theorem nlChkAt_eq (ns s t : List Nat) :
    nlChkAt E lens ns s t = nlChk E lens ns (lnth 0 s 0) (lnth 0 s 1) (lnth 0 s 2) (lnth 0 s 3)
      (lnth 0 s 4) (lnth 0 s 5)
        (nlAt (lnth 0 t 0) (lnth 0 t 1) (lnth 0 t 2) (lnth 0 t 3) (lnth 0 t 4) (lnth 0 t 5)) := by
  simp only [nlChkAt, forceN_eq]

theorem nlChk_chunks (fin : Nat → Nat → Nat → Nat → Nat → Nat → Bool) :
    ∀ (cs : List (List Char)) (S : Nat → List Nat),
      (∀ j < cs.length, nlChkAt E lens ((lnth [] cs j).map Char.toNat) (S j) (S (j + 1)) = true) →
      fin (lnth 0 (S cs.length) 0) (lnth 0 (S cs.length) 1) (lnth 0 (S cs.length) 2)
        (lnth 0 (S cs.length) 3) (lnth 0 (S cs.length) 4) (lnth 0 (S cs.length) 5) = true →
      nlChk E lens (cs.flatten.map Char.toNat) (lnth 0 (S 0) 0) (lnth 0 (S 0) 1) (lnth 0 (S 0) 2)
        (lnth 0 (S 0) 3) (lnth 0 (S 0) 4) (lnth 0 (S 0) 5) fin = true
  | [], S, _, hf => hf
  | c :: cs, S, h, hf => by
    rw [List.flatten_cons, List.map_append]
    have h0 := h 0 (by simp)
    rw [lnth_cons_zero, nlChkAt_eq] at h0
    refine nlChk_append_at E lens h0 (nlChk_chunks fin cs (fun j => S (j + 1)) (fun j hj => ?_) hf)
    have := h (j + 1) (by simp; omega)
    rwa [lnth_cons_succ] at this

end Join

end CFSG.KS.RouteP
