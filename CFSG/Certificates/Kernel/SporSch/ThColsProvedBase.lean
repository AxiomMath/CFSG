
module

public import CFSG.Certificates.Kernel.SporSch.ThRowsProved

@[expose] public section

namespace CFSG.KS.SporSch.Pf

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th
open Finset
open scoped Matrix

@[expose] def parStep (y j acc : Nat) : Nat := Nat.xor acc (Nat.land (Nat.shiftRight y j) 1)

theorem bit_one (y j : Nat) : Nat.land (Nat.shiftRight y j) 1 = if y.testBit j then 1 else 0 := by
  change (y >>> j) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (y / 2 ^ j) with h | h <;> simp [h]

@[expose] def colStep (c : Nat → Bool) (i acc : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft 1 i)) (c i)

theorem testBit_colFold (c : Nat → Bool) (k : Nat) : ∀ l : List Nat,
    (l.foldr (colStep c) 0).testBit k = l.any fun i => (i == k) && c i
  | [] => by simp
  | i :: l => by
    rw [List.foldr_cons, List.any_cons, ← testBit_colFold c k l, colStep]
    cases c i
    · simp
    · change ((l.foldr (colStep c) 0) ||| (1 <<< i)).testBit k = _
      rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, Bool.or_comm]
      by_cases h : i = k <;> simp [h]

theorem testBit_colK (R : Nat → Nat) (x k : Nat) : (colK R x).testBit k =
    (decide (k < 248) && Nat.beq (par248 (Nat.land (R k) x)) 1) := by
  have e : colK R x = (List.range 248).foldr
      (colStep fun i => Nat.beq (par248 (Nat.land (R i) x)) 1) 0 := by
    rw [colK, CFSG.KC.Pack.foldN_eq]
    rfl
  rw [e, testBit_colFold]
  by_cases hk : k < 248
  · have : (List.range 248).any (fun i => (i == k) && Nat.beq (par248 (Nat.land (R i) x)) 1) =
        Nat.beq (par248 (Nat.land (R k) x)) 1 := by
      apply Bool.eq_iff_iff.2
      rw [List.any_eq_true]
      constructor
      · rintro ⟨i, -, h⟩
        rw [Bool.and_eq_true, beq_iff_eq] at h
        rw [← h.1]
        exact h.2
      · intro h
        exact ⟨k, List.mem_range.2 hk, by rw [Bool.and_eq_true, beq_iff_eq]; exact ⟨rfl, h⟩⟩
    rw [this]
    simp [hk]
  · rw [decide_eq_false hk, Bool.false_and]
    apply Bool.eq_false_iff.2
    intro h
    rw [List.any_eq_true] at h
    obtain ⟨i, hi, h⟩ := h
    rw [Bool.and_eq_true, beq_iff_eq] at h
    rw [List.mem_range] at hi
    omega

theorem colK_lt (R : Nat → Nat) (x : Nat) : colK R x < 2 ^ 248 :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by
    rw [testBit_colK, decide_eq_false (by omega), Bool.false_and]

theorem v4OfNat_xor {a b : Nat} (ha : a < 2 ^ 248) (hb : b < 2 ^ 248) :
    (v4OfNat a).xor (v4OfNat b) = v4OfNat (Nat.xor a b) := by
  have hab : Nat.xor a b < 2 ^ 248 := Nat.xor_lt_two_pow ha hb
  apply V4.eq_of_toVec_eq (V4.xor_wf (v4OfNat_wf ha) (v4OfNat_wf hb)) (v4OfNat_wf hab)
  funext j
  rw [V4.toVec_xor, Pi.add_apply, toVec_v4OfNat, toVec_v4OfNat, toVec_v4OfNat, rowOfNat_xor]
  rfl

theorem v4_lt {a b : Nat} (ha : a < 2 ^ 248) (hb : b < 2 ^ 248) :
    (v4OfNat a).lt (v4OfNat b) = Nat.blt a b := by
  apply Bool.eq_iff_iff.2
  rw [V4.lt_iff, v4OfNat_toNat_of_lt ha, v4OfNat_toNat_of_lt hb, Nat.blt_eq]

theorem v4_lt' (a b : Nat) : (v4OfNat a).lt (v4OfNat b) = Nat.blt (a % 2 ^ 256) (b % 2 ^ 256) := by
  apply Bool.eq_iff_iff.2
  rw [V4.lt_iff, v4OfNat_toNat, v4OfNat_toNat, Nat.blt_eq]

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem lor_shift_mod {x y : Nat} (hx : x < 2 ^ 256) :
    Nat.lor x (Nat.shiftLeft y 256) % 2 ^ 256 = x ∧ Nat.lor x (Nat.shiftLeft y 256) / 2 ^ 256 = y := by
  have e : Nat.lor x (Nat.shiftLeft y 256) = x + 2 ^ 256 * y := by
    change x ||| (y <<< 256) = _
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm,
      Nat.mul_comm]
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  · rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 256), Nat.div_eq_of_lt hx, Nat.zero_add]

end CFSG.KS.SporSch.Pf

end

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th
open CFSG.KS.SporSch.Pf
open Finset
open scoped Matrix

theorem canonN_sound_proved {a b : Nat} (ha : a < 2 ^ 248) (hb : b < 2 ^ 248) :
    canon (v4OfNat a) (v4OfNat b) =
      ⟨v4OfNat (canonN a b % 2 ^ 256), v4OfNat (canonN a b / 2 ^ 256)⟩ := by
  have hs : Nat.xor a b < 2 ^ 248 := Nat.xor_lt_two_pow ha hb
  have h256 : ∀ {z : Nat}, z < 2 ^ 248 → z < 2 ^ 256 := fun hz => lt_trans hz (by norm_num)
  have ma := Nat.mod_eq_of_lt (h256 ha)
  have mb := Nat.mod_eq_of_lt (h256 hb)
  have ms := Nat.mod_eq_of_lt (h256 hs)
  have la' := lor_shift_mod (y := b) (h256 ha)
  have lb' := lor_shift_mod (y := a) (h256 hb)
  have ls1 := lor_shift_mod (y := a) (h256 hs)
  have ls2 := lor_shift_mod (y := b) (h256 hs)
  have la2 := lor_shift_mod (y := Nat.xor a b) (h256 ha)
  have lb2 := lor_shift_mod (y := Nat.xor a b) (h256 hb)
  unfold canon canonN
  simp only [strictN_eq']
  rw [v4OfNat_xor ha hb]
  generalize Nat.xor a b = s at ms ls1 ls2 la2 lb2
  cases h1 : Nat.blt b a <;> cases h2 : Nat.blt a b <;> cases h3 : Nat.blt s a <;>
    cases h4 : Nat.blt s b <;>
    simp only [v4_lt', ma, mb, ms, h1, h2, h3, h4, Bool.false_eq_true, ite_false, ite_true,
      la'.1, la'.2, lb'.1, lb'.2, ls1.1, ls1.2, ls2.1, ls2.2,
      la2.1, la2.2, lb2.1, lb2.2]

end CFSG.KS.SporSch

end
