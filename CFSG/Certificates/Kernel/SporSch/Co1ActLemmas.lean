module

public import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas

public section

namespace CFSG.KS.SporSch.M24.ActL

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.KS.Raw

@[expose] def xs (f : Nat → Bool) (l : List Nat) : Bool := l.foldr (fun j b => f j ^^ b) false

theorem xs_nil (f : Nat → Bool) : xs f [] = false := rfl

theorem xs_cons (f : Nat → Bool) (a : Nat) (l : List Nat) : xs f (a :: l) = (f a ^^ xs f l) := rfl

theorem xs_append (f : Nat → Bool) (l₁ l₂ : List Nat) : xs f (l₁ ++ l₂) = (xs f l₁ ^^ xs f l₂) := by
  induction l₁ with
  | nil => simp [xs_nil]
  | cons a l ih => rw [List.cons_append, xs_cons, xs_cons, ih, Bool.xor_assoc]

theorem xs_map (f : Nat → Bool) (g : Nat → Nat) (l : List Nat) :
    xs f (l.map g) = xs (fun k => f (g k)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, xs_cons, xs_cons, ih]

theorem xs_xor (f g : Nat → Bool) (l : List Nat) :
    xs (fun k => f k ^^ g k) l = (xs f l ^^ xs g l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [xs_cons, xs_cons, xs_cons, ih]
    cases f a <;> cases g a <;> cases xs f l <;> cases xs g l <;> rfl

theorem xs_congr {f g : Nat → Bool} {l : List Nat} (h : ∀ j ∈ l, f j = g j) : xs f l = xs g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [xs_cons, xs_cons, h a (List.mem_cons_self ..),
      ih fun j hj => h j (List.mem_cons_of_mem a hj)]

theorem xs_false (l : List Nat) : xs (fun _ => false) l = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [xs_cons, ih]
    rfl

@[expose] def sx (x s : Nat) : Nat := x ^^^ x >>> s

theorem xs_sx (x s t : Nat) (ht : t = s + s) :
    xs (fun k => (sx x s).testBit k) (List.range s) = xs (fun k => x.testBit k) (List.range t) := by
  subst ht
  rw [List.range_add, xs_append, xs_map]
  simp only [sx, Nat.testBit_xor, Nat.testBit_shiftRight]
  exact xs_xor _ _ _

theorem parK_eq (x : Nat) : parK x = sx (sx (sx (sx (sx x 16) 8) 4) 2) 1 &&& 1 := by
  simp only [parK, MatL.strictN_eq]
  rfl

theorem and_one_beq (y : Nat) : Nat.beq (y &&& 1) 1 = y.testBit 0 := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> rw [h] <;> rfl

theorem parK_and (r v : Nat) (hr : r < 2 ^ 24) :
    Nat.beq (parK (Nat.land r v)) 1 = xs (fun j => r.testBit j && v.testBit j) (List.range 24) := by
  have hb : ∀ k, 24 ≤ k → r.testBit k = false := fun k hk =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) hk))
  have h1 : ∀ y : Nat, y.testBit 0 = xs (fun k => y.testBit k) (List.range 1) := by
    intro y
    simp [xs]
  have e32 : (32 : Nat) = 24 + 8 := rfl
  have eland : Nat.land r v = r &&& v := rfl
  rw [parK_eq, and_one_beq, h1, xs_sx _ 1 2 rfl, xs_sx _ 2 4 rfl, xs_sx _ 4 8 rfl,
    xs_sx _ 8 16 rfl, xs_sx _ 16 32 rfl, e32,
    List.range_add, xs_append, xs_map, eland]
  rw [xs_congr (g := fun _ => false) (l := List.range 8), xs_false, Bool.xor_false]
  · exact xs_congr fun j _ => Nat.testBit_and ..
  · intro j _
    rw [Nat.testBit_and, hb _ (by omega), Bool.false_and]

theorem testBit_vecMulN_aux (v : Nat) (Y : Array Nat) (i : Nat) (L : List Nat) (acc : Nat) :
    (L.foldl (fun acc j => if v.testBit j then acc ^^^ (Y[j]?.getD 0) else acc) acc).testBit i =
      (acc.testBit i ^^ xs (fun j => v.testBit j && (Y[j]?.getD 0).testBit i) L) := by
  induction L generalizing acc with
  | nil => simp [xs_nil]
  | cons a L ih =>
    rw [List.foldl_cons, ih, xs_cons]
    by_cases h : v.testBit a = true <;> simp [h, Nat.testBit_xor]

theorem testBit_vecMulN (d : Nat) (Y : Array Nat) (v i : Nat) :
    (vecMulN d Y v).testBit i =
      xs (fun j => v.testBit j && (Y[j]?.getD 0).testBit i) (List.range d) := by
  rw [vecMulN, testBit_vecMulN_aux]
  simp

theorem testBit_ofBits_aux (f : Nat → Bool) (i : Nat) (L : List Nat) (acc : Nat) :
    (L.foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) acc).testBit i =
      (acc.testBit i || (decide (i ∈ L) && f i)) := by
  induction L generalizing acc with
  | nil => simp
  | cons a L ih =>
    rw [List.foldl_cons, ih]
    by_cases hi : a = i
    · subst hi
      by_cases h : f a = true <;> simp [h, Nat.testBit_or, Nat.one_shiftLeft]
    · by_cases h : f a = true <;>
        simp [h, hi, Ne.symm hi, Nat.testBit_or, Nat.one_shiftLeft]

theorem testBit_ofBits (d : Nat) (f : Nat → Bool) (i : Nat) :
    (ofBits d f).testBit i = (decide (i < d) && f i) := by
  rw [ofBits, testBit_ofBits_aux]
  simp

theorem testBit_foldr_or (f : Nat → Bool) (i : Nat) (L : List Nat) :
    (L.foldr (fun j s => if f j = true then Nat.lor s (Nat.shiftLeft 1 j) else s) 0).testBit i =
      (decide (i ∈ L) && f i) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons]
    have e : ∀ x y : Nat, Nat.lor x (Nat.shiftLeft 1 y) = x ||| 1 <<< y := fun _ _ => rfl
    by_cases h : f a = true
    · rw [ite_eq_left h, e, Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hi : a = i
      · subst hi
        simp [h]
      · simp [hi, Ne.symm hi]
    · rw [ite_eq_right h, ih]
      by_cases hi : a = i
      · subst hi
        simp [h]
      · simp [Ne.symm hi]

theorem actK_eq_foldr (X v : Nat) : actK X v = (List.range 24).foldr (fun i s =>
    if Nat.beq (parK (Nat.land (rowK X i) v)) 1 = true then Nat.lor s (Nat.shiftLeft 1 i)
    else s) 0 := by
  rw [actK, MatL.foldN_eq]
  simp only [MatL.nIf_eq]

theorem rowK_lt (X i : Nat) : rowK X i < 2 ^ 24 := by
  have e : rowK X i = (X >>> (24 * i)) &&& 16777215 := rfl
  rw [e]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem pg_rowK (P i : Nat) : pg 24 (mask 24) P i = rowK P i := rfl

theorem vecMulN_unpack (P v : Nat) :
    vecMulN 24 (transposeRows 24 (unpack 24 24 P)) v = actK P v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_vecMulN, actK_eq_foldr, testBit_foldr_or, parK_and _ _ (rowK_lt P i)]
  by_cases hi : i < 24
  · simp only [List.mem_range, hi, decide_true, Bool.true_and]
    apply xs_congr
    intro j hj
    rw [List.mem_range] at hj
    simp only [transposeRows, Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some,
      testBit_ofBits, unpack, pg_rowK, hi, decide_true, Bool.true_and, Bool.and_comm]
  · simp only [List.mem_range, hi, decide_false, Bool.false_and]
    rw [xs_congr (g := fun _ => false), xs_false]
    intro j hj
    rw [List.mem_range] at hj
    simp only [transposeRows, Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some,
      testBit_ofBits, hi, decide_false, Bool.false_and, Bool.and_false]

theorem act_unpack (P v : Nat) : act (unpack 24 24 P) v = actK P v := vecMulN_unpack P v

end CFSG.KS.SporSch.M24.ActL

end
