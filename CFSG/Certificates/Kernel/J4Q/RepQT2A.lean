module

public import CFSG.Certificates.Kernel.J4Q.RepQT
public import CFSG.Sporadic.J4.QT2ANative

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem char_le_iff (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]
  rfl

theorem w5_char (ch : Char) :
    (if 'a' ≤ ch ∧ ch ≤ 'e' then some ((ch.toNat - 'a'.toNat + 1 : Nat) : Int)
      else if 'A' ≤ ch ∧ ch ≤ 'E' then some (-((ch.toNat - 'A'.toNat + 1 : Nat) : Int))
      else none) =
    Bool.rec (motive := fun _ => Option Int)
      (Bool.rec (motive := fun _ => Option Int) none (some (Int.negSucc (ch.toNat - 65)))
        (andB (Nat.ble 65 ch.toNat) (Nat.ble ch.toNat 69)))
      (some (Int.ofNat (ch.toNat - 96))) (andB (Nat.ble 97 ch.toNat) (Nat.ble ch.toNat 101)) := by
  have ble_dec : ∀ a b : Nat, Nat.ble a b = decide (a ≤ b) := by
    intro a b
    by_cases h : a ≤ b
    · rw [decide_eq_true h]
      exact Nat.ble_eq.mpr h
    · rw [decide_eq_false h]
      cases hb : Nat.ble a b
      · rfl
      · exact absurd (Nat.ble_eq.mp hb) h
  simp only [char_le_iff, andB_eq, ble_dec]
  have ha : 'a'.toNat = 97 := rfl
  have he : 'e'.toNat = 101 := rfl
  have hA : 'A'.toNat = 65 := rfl
  have hE : 'E'.toNat = 69 := rfl
  rw [ha, he, hA, hE]
  by_cases h1 : 97 ≤ ch.toNat ∧ ch.toNat ≤ 101
  · simp only [h1, and_self, ↓reduceIte, decide_true, Bool.and_self, Option.some.injEq]
    rw [Int.ofNat_eq_natCast, Nat.cast_inj]
    omega
  · have h1' : (decide (97 ≤ ch.toNat) && decide (ch.toNat ≤ 101)) = false := by
      rw [← Bool.decide_and, decide_eq_false h1]
    simp only [h1, ↓reduceIte, h1']
    by_cases h2 : 65 ≤ ch.toNat ∧ ch.toNat ≤ 69
    · simp only [h2, and_self, ↓reduceIte, decide_true, Bool.and_self, Option.some.injEq]
      rw [Int.negSucc_eq]
      push_cast
      omega
    · have h2' : (decide (65 ≤ ch.toNat) && decide (ch.toNat ≤ 69)) = false := by
        rw [← Bool.decide_and, decide_eq_false h2]
      simp only [h2, ↓reduceIte, h2']

theorem w5_ofList (cs : List Char) : w5 (String.ofList cs) = w5K cs := by
  unfold w5
  rw [String.toList_ofList]
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    rw [List.filterMap_cons, w5_char ch, ih]
    change _ = Bool.rec (motive := fun _ => List Int)
      (Bool.rec (motive := fun _ => List Int) (w5K cs)
        (List.cons (Int.negSucc (Nat.sub ch.toNat 65)) (w5K cs))
        (andB (Nat.ble 65 ch.toNat) (Nat.ble ch.toNat 69)))
      (List.cons (Int.ofNat (Nat.sub ch.toNat 96)) (w5K cs))
      (andB (Nat.ble 97 ch.toNat) (Nat.ble ch.toNat 101))
    cases andB (Nat.ble 97 ch.toNat) (Nat.ble ch.toNat 101) <;>
      cases andB (Nat.ble 65 ch.toNat) (Nat.ble ch.toNat 69) <;> rfl

theorem allNe_enc (x : Array V2) (hx : WfA x) :
    ∀ (L : List (Array V2)), (∀ y ∈ L, WfA y) →
      L.all (fun y => !eqRows x y) = allNeK (encR x) (L.map encR)
  | [], _ => rfl
  | y :: L, h => by
    rw [List.all_cons, List.map_cons, eqRows_eq hx (h y List.mem_cons_self),
      allNe_enc x hx L (fun z hz => h z (List.mem_cons_of_mem _ hz))]
    change _ = andB (neN (encR x) (encR y)) _
    rw [andB_eq]
    rfl

theorem allDistinct_enc : ∀ (L : List (Array V2)), (∀ X ∈ L, WfA X) →
    allDistinct L = distinctK (L.map encR)
  | [], _ => rfl
  | x :: L, h => by
    have hL : ∀ X ∈ L, WfA X := fun X hX => h X (List.mem_cons_of_mem _ hX)
    rw [allDistinct, allNe_enc x (h x List.mem_cons_self) L hL, allDistinct_enc L hL,
      List.map_cons]
    change _ = andB _ _
    rw [andB_eq]
    rfl

end CFSG.KC.J4Q

end
