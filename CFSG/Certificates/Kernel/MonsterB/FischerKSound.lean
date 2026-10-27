module

public import Certificates.Data.Kernel.MonsterB.FischerK
public import Certificates.Data.CFSGNative.HS.SmallF2
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.FischerK

open CFSG.Sporadic.SmallF2.Native CFSG.KLie.CT

theorem vecMulL_nil (v : Nat) : vecMulL [] v = 0 := rfl

theorem vecMulL_cons (r : Nat) (R : List Nat) (v : Nat) :
    vecMulL (r :: R) v = (if v.testBit 0 then r else 0) ^^^ vecMulL R (v / 2) := by
  change Nat.xor (Bool.rec (motive := fun _ => Nat) 0 r (Nat.beq (Nat.land v 1) 1))
    (vecMulL R (Nat.shiftRight v 1)) = _
  have h1 : Nat.shiftRight v 1 = v / 2 := by
    have := Nat.shiftRight_eq_div_pow v 1
    simpa using this
  rw [h1]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one v with h | h
  · have h0 : Nat.land v 1 = 0 := by
      change v &&& 1 = 0
      rw [Nat.and_one_is_mod, h]
    have hb : v.testBit 0 = false := by
      rw [Nat.testBit_zero]
      simp [h]
    rw [h0, hb]
    simp <;> rfl
  · have h0 : Nat.land v 1 = 1 := by
      change v &&& 1 = 1
      rw [Nat.and_one_is_mod, h]
    have hb : v.testBit 0 = true := by
      rw [Nat.testBit_zero]
      simp [h]
    rw [h0, hb]
    simp <;> rfl

private def stepN (R : List Nat) (v acc j : Nat) : Nat :=
  if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc

private theorem foldl_eq : ∀ (R : List Nat) (v acc : Nat),
    (List.range R.length).foldl (stepN R v) acc = acc ^^^ vecMulL R v
  | [], v, acc => by simp [vecMulL_nil]
  | r :: R, v, acc => by
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have hstep : (fun acc j => stepN (r :: R) v acc (j + 1)) = stepN R (v / 2) := by
      funext acc j
      unfold stepN
      rw [Nat.testBit_succ, List.getElem?_cons_succ]
    rw [hstep, foldl_eq R (v / 2), vecMulL_cons]
    unfold stepN
    by_cases hb : v.testBit 0 <;> simp [hb, Nat.xor_assoc]

theorem vecMulN_eq {d : Nat} {R : Array Nat} (hR : R.size = d) (v : Nat) :
    vecMulN d R v = vecMulL R.toList v := by
  have h := foldl_eq R.toList v 0
  rw [Nat.zero_xor, Array.length_toList, hR] at h
  rw [← h, vecMulN]
  congr 1
  funext acc j
  unfold stepN
  rw [Array.getElem?_toList]

theorem allIdx_iff (p : Nat → Nat → Bool) : ∀ (L : List Nat) (i : Nat),
    allIdx p L i = true ↔ ∀ k (hk : k < L.length), p (i + k) L[k] = true
  | [], i => by simp [allIdx]
  | r :: L, i => by
    change Bool.rec (motive := fun _ => Bool) false (allIdx p L (Nat.succ i)) (p i r) = true ↔ _
    have ih := allIdx_iff p L (i + 1)
    have h0 : p (i + 0) (r :: L)[0] = p i r := rfl
    cases hpr : p i r
    · constructor
      · intro h
        exact absurd h Bool.false_ne_true
      · intro h
        have := h 0 (by simp)
        rw [h0, hpr] at this
        exact absurd this Bool.false_ne_true
    · change allIdx p L (i + 1) = true ↔ _
      rw [ih]
      constructor
      · intro h k hk
        cases k with
        | zero => rw [h0, hpr]
        | succ k =>
          have := h k (by simpa using hk)
          have e : i + 1 + k = i + (k + 1) := by omega
          rw [e] at this
          exact this
      · intro h k hk
        have := h (k + 1) (by simpa using hk)
        have e : i + 1 + k = i + (k + 1) := by omega
        rw [e]
        exact this

theorem all_range_congr {n : Nat} {p q : Nat → Bool} (h : ∀ i < n, p i = q i) :
    (List.range n).all p = (List.range n).all q := by
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun i hi => by rw [h i (List.mem_range.1 hi)]

theorem range_all_eq_allIdx (p : Nat → Nat → Bool) (L : List Nat) :
    ((List.range L.length).all fun q => p q L.toArray[q]!) = allIdx p L 0 := by
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true, allIdx_iff]
  constructor
  · intro h k hk
    have := h k (List.mem_range.2 hk)
    simpa [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, hk] using this
  · intro h q hq
    have hq' := List.mem_range.1 hq
    have := h q hq'
    simpa [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, hq'] using this

theorem packW_spec (w M : Nat) : ∀ (L : List Nat) (i : Nat), packW w M L i = true →
    ∀ k (hk : k < L.length), L[k] = fget M (i + k) w
  | [], _, _ => fun k hk => absurd hk (by simp)
  | r :: L, i, h => by
    change Bool.rec (motive := fun _ => Bool) false (packW w M L (Nat.succ i))
      (Nat.beq r (fget M i w)) = true at h
    cases hr : Nat.beq r (fget M i w)
    · rw [hr] at h
      exact absurd h Bool.false_ne_true
    · rw [hr] at h
      intro k hk
      cases k with
      | zero => simpa using Nat.eq_of_beq_eq_true hr
      | succ k =>
        have := packW_spec w M L (i + 1) h k (by simpa using hk)
        have e : i + 1 + k = i + (k + 1) := by omega
        rw [List.getElem_cons_succ, this, e]

theorem packW_get {w M : Nat} {L : List Nat} (h : packW w M L 0 = true) {k : Nat}
    (hk : k < L.length) : L.toArray[k]! = fget M k w := by
  have := packW_spec w M L 0 h k hk
  simpa [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, hk] using this

end CFSG.KC.FischerK

end
