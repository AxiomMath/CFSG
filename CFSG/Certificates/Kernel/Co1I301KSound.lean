module

public import Certificates.Data.Kernel.Co1I301K
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.Sporadic.Co1I301.Inputs

public section

namespace CFSG.KC.Co1I301

open CFSG.KLie.CT CFSG.KC.Co1F2 CFSG.KC.Co1B

theorem zipK_cons (a : Nat) (A : List Nat) (b : Nat) (B : List Nat) :
    zipK (a :: A) (b :: B) = (a, b) :: zipK A B := rfl

theorem zipK_length : ∀ {A B : List Nat}, A.length = B.length → (zipK A B).length = A.length
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (by simp)
  | a :: A, b :: B, h => by
    rw [zipK_cons, List.length_cons, List.length_cons, zipK_length (by simpa using h)]

theorem zipK_fst : ∀ {A B : List Nat}, A.length = B.length → (zipK A B).map Prod.fst = A
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (by simp)
  | a :: A, b :: B, h => by
    rw [zipK_cons, List.map_cons, zipK_fst (by simpa using h)]

theorem zipK_snd : ∀ {A B : List Nat}, A.length = B.length → (zipK A B).map Prod.snd = B
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | a :: A, b :: B, h => by
    rw [zipK_cons, List.map_cons, zipK_snd (by simpa using h)]

theorem co1I301_andB (a b : Bool) : CFSG.KLie.CT.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [CFSG.KLie.CT.andB]

theorem eqListK_sound {F : Nat → Nat} : ∀ {L : List Nat} {k : Nat}, eqListK F L k = true →
    ∀ i (hi : i < L.length), L[i] = F (k + i)
  | [], _, _, i, hi => absurd hi (by simp)
  | a :: L, k, h, i, hi => by
    have h' : CFSG.KLie.CT.andB (Nat.beq a (F k)) (eqListK F L (Nat.succ k)) = true := h
    rw [co1I301_andB] at h'
    cases i with
    | zero => exact Nat.eq_of_beq_eq_true h'.1
    | succ i =>
      rw [List.getElem_cons_succ, eqListK_sound h'.2 i (by simpa using hi)]
      congr 1
      omega

theorem impAllK_sound {p q : Nat → Bool} : ∀ {L : List Nat}, impAllK p q L = true →
    ∀ x ∈ L, p x = true → q x = true
  | [], _, x, hx, _ => absurd hx List.not_mem_nil
  | y :: L, h, x, hx, hp => by
    have h' : CFSG.KLie.CT.andB (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (p y)) (q y)) (impAllK p q L) = true := h
    rw [co1I301_andB] at h'
    rcases List.mem_cons.1 hx with rfl | hx
    · have h1 := h'.1
      rw [hp] at h1
      exact h1
    · exact impAllK_sound h'.2 x hx hp

theorem relK_sound (x y xi yi : Nat) (w : List (Fin 2 × Bool)) :
    CFSG.Sporadic.Co1I301.Native.relRows (unpackR 24 x) (unpackR 24 y) (unpackR 24 xi)
      (unpackR 24 yi) w = unpackR 24 (relK x y xi yi w) := by
  unfold CFSG.Sporadic.Co1I301.Native.relRows relK
  rw [one_eq]
  generalize oneK = a
  induction w generalizing a with
  | nil => rfl
  | cons l w ih =>
    rw [List.foldl_cons, List.foldl_cons, ← ih]
    refine congrArg (fun z => List.foldl _ z w) ?_
    change CFSG.Sporadic.Co1Schreier.Native.mul (unpackR 24 a) _ = unpackR 24 (mulWK a _)
    have e : (if l.1 = 0 then (if l.2 = true then unpackR 24 x else unpackR 24 xi) else
        (if l.2 = true then unpackR 24 y else unpackR 24 yi)) =
        unpackR 24 (if l.1 = 0 then (if l.2 = true then x else xi) else
          (if l.2 = true then y else yi)) := by
      split <;> split <;> rfl
    rw [e, CFSG.KC.F2W.mul_unpackW]
    rfl

end CFSG.KC.Co1I301

end
