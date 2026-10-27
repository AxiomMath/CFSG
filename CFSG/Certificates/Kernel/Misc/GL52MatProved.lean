module

public import CFSG.Certificates.Kernel.Misc.GL52MatCode
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.Misc.GLM.Pf

open CFSG.KC.Misc.GLM

theorem pack_spec (w : Nat) : ∀ (k : Nat) (f : Fin k → Nat), (∀ i, f i < 2 ^ w) →
    (∑ i : Fin k, f i * 2 ^ (w * (i : Nat))) < 2 ^ (w * k) ∧
      ∀ (i : Fin k) (j : Nat), j < w →
        (∑ i : Fin k, f i * 2 ^ (w * (i : Nat))).testBit (w * i + j) = (f i).testBit j
  | 0, _, _ => ⟨by simp, fun i => i.elim0⟩
  | k + 1, f, hf => by
    obtain ⟨hlt, hbit⟩ := pack_spec w k (fun i => f i.castSucc) (fun i => hf _)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have e : ∀ S, S + f (Fin.last k) * 2 ^ (w * k) = 2 ^ (w * k) * f (Fin.last k) + S :=
      fun S => by rw [Nat.add_comm, Nat.mul_comm]
    rw [e]
    refine ⟨?_, fun i j hj => ?_⟩
    · have h1 : 2 ^ (w * k) * f (Fin.last k) + _ < 2 ^ (w * k) * f (Fin.last k) + 2 ^ (w * k) :=
        Nat.add_lt_add_left hlt _
      have h2 : 2 ^ (w * k) * (f (Fin.last k) + 1) ≤ 2 ^ (w * k) * 2 ^ w :=
        Nat.mul_le_mul_left _ (hf _)
      rw [Nat.mul_succ] at h2
      rw [Nat.mul_succ, Nat.pow_add]
      exact Nat.lt_of_lt_of_le h1 h2
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.val_last, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_right (by omega),
          Nat.add_sub_cancel_left]
      · have hi : w * ((i : Nat) + 1) ≤ w * k := Nat.mul_le_mul_left w i.isLt
        rw [Nat.mul_succ] at hi
        rw [Fin.val_castSucc, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_left (by omega)]
        exact hbit i j hj

@[expose] def zb (x : ZMod 2) : Bool := x.val.testBit 0

theorem zb_inj : ∀ {x y : ZMod 2}, zb x = zb y → x = y := by decide

theorem zb_add : ∀ x y : ZMod 2, zb (x + y) = (zb x ^^ zb y) := by decide

theorem zb_mul : ∀ x y : ZMod 2, zb (x * y) = (zb x && zb y) := by decide

theorem mcode_eq (A : Mat) : mcode A =
    ∑ i : Fin 5, (∑ j : Fin 5, (A i j).val * 2 ^ (1 * (j : Nat))) * 2 ^ (5 * (i : Nat)) := by
  unfold mcode
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.one_mul, Nat.pow_add]
  ring

theorem entry_lt (A : Mat) (i j : Fin 5) : (A i j).val < 2 ^ 1 := ZMod.val_lt _

theorem row_lt (A : Mat) (i : Fin 5) : (∑ j : Fin 5, (A i j).val * 2 ^ (1 * (j : Nat))) < 2 ^ 5 :=
  (pack_spec 1 5 _ (entry_lt A i)).1

theorem mcode_lt (A : Mat) : mcode A < 2 ^ 25 := by
  rw [mcode_eq]
  exact (pack_spec 5 5 _ (row_lt A)).1

theorem mcode_bit (A : Mat) (i j : Fin 5) : (mcode A).testBit (5 * i + j) = zb (A i j) := by
  rw [mcode_eq, (pack_spec 5 5 _ (row_lt A)).2 i j j.isLt]
  have h := (pack_spec 1 5 _ (entry_lt A i)).2 j 0 (by decide)
  have e : (j : Nat) = 1 * j + 0 := by omega
  rw [e]
  exact h

theorem bitK_eq (x i : Nat) : bitK x i = x.testBit i := by
  have e : Nat.land (Nat.shiftRight x i) 1 = x / 2 ^ i % 2 := by
    change (x >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold bitK
  change Nat.beq (Nat.land (Nat.shiftRight x i) 1) 1 = _
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem rowK_bit (c i j : Nat) : (rowK c i).testBit j = (decide (j < 5) && c.testBit (5 * i + j)) := by
  unfold rowK
  change ((c >>> (5 * i)) &&& (2 ^ 5 - 1)).testBit j = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

@[expose] def xorN (g : Nat → Bool) (m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => acc ^^ g k) m

theorem xorN_false {g : Nat → Bool} (h : ∀ k, g k = false) : ∀ m, xorN g m = false
  | 0 => rfl
  | m + 1 => by
    change (xorN g m ^^ g m) = false
    rw [xorN_false h m, h m]
    rfl

theorem xorN_five (g : Nat → Bool) : xorN g 5 = (((((false ^^ g ((0 : Fin 5) : Nat)) ^^
    g ((1 : Fin 5) : Nat)) ^^ g ((2 : Fin 5) : Nat)) ^^ g ((3 : Fin 5) : Nat)) ^^
    g ((4 : Fin 5) : Nat)) := rfl

@[expose] noncomputable def selR (r b m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (rowK b k)) (bitK r k)) m

theorem selK_eq (r b : Nat) : selK r b = selR r b 5 := rfl

theorem selR_bit (r b j : Nat) : ∀ m,
    (selR r b m).testBit j = xorN (fun k => r.testBit k && (rowK b k).testBit j) m
  | 0 => Nat.zero_testBit j
  | m + 1 => by
    change (Bool.rec (motive := fun _ => Nat) (selR r b m) (Nat.xor (selR r b m) (rowK b m))
      (bitK r m)).testBit j = (xorN _ m ^^ (r.testBit m && (rowK b m).testBit j))
    rw [bitK_eq]
    cases r.testBit m
    · change (selR r b m).testBit j = _
      rw [selR_bit r b j m, Bool.false_and, Bool.xor_false]
    · change ((selR r b m) ^^^ (rowK b m)).testBit j = _
      rw [Nat.testBit_xor, selR_bit r b j m, Bool.true_and]

theorem selK_high (r b j : Nat) (hj : 5 ≤ j) : (selK r b).testBit j = false := by
  rw [selK_eq, selR_bit]
  exact xorN_false (fun k => by rw [rowK_bit, decide_eq_false (by omega)]; simp) 5

@[expose] noncomputable def mulR (a b m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (selK (rowK a i) b) (Nat.mul 5 i))) m

theorem mmulK_eq (a b : Nat) : mmulK a b = mulR a b 5 := rfl

theorem mulR_bit (a b i0 j0 : Nat) (hj : j0 < 5) : ∀ m,
    (mulR a b m).testBit (5 * i0 + j0) = (decide (i0 < m) && (selK (rowK a i0) b).testBit j0)
  | 0 => by
    change (0 : Nat).testBit _ = _
    rw [Nat.zero_testBit, decide_eq_false (Nat.not_lt_zero _), Bool.false_and]
  | m + 1 => by
    change ((mulR a b m) ||| ((selK (rowK a m) b) <<< (5 * m))).testBit (5 * i0 + j0) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, mulR_bit a b i0 j0 hj m]
    rcases Nat.lt_trichotomy i0 m with h | rfl | h
    · rw [decide_eq_true h, decide_eq_true (by omega : i0 < m + 1),
        decide_eq_false (by omega : ¬ (5 * i0 + j0 ≥ 5 * m))]
      simp
    · rw [decide_eq_false (Nat.lt_irrefl _), decide_eq_true (by omega : i0 < i0 + 1),
        decide_eq_true (by omega : 5 * i0 + j0 ≥ 5 * i0), Nat.add_sub_cancel_left]
      simp
    · rw [decide_eq_false (by omega : ¬ i0 < m), decide_eq_false (by omega : ¬ i0 < m + 1),
        selK_high _ _ (5 * i0 + j0 - 5 * m) (by omega)]
      simp

theorem sel_bit (A B : Mat) (i j : Fin 5) :
    (selK (rowK (mcode A) i) (mcode B)).testBit j = zb ((A * B) i j) := by
  have hg : ∀ k : Fin 5, ((rowK (mcode A) i).testBit k && (rowK (mcode B) k).testBit j) =
      (zb (A i k) && zb (B k j)) := fun k => by
    rw [rowK_bit, rowK_bit, decide_eq_true k.isLt, decide_eq_true j.isLt, Bool.true_and,
      Bool.true_and, mcode_bit, mcode_bit]
  rw [selK_eq, selR_bit, xorN_five, hg 0, hg 1, hg 2, hg 3, hg 4, Matrix.mul_apply,
    Fin.sum_univ_five, zb_add, zb_add, zb_add, zb_add, zb_mul, zb_mul, zb_mul, zb_mul, zb_mul,
    Bool.false_xor]

end CFSG.KC.Misc.GLM.Pf

end

public section

namespace CFSG.KC.Misc.GLM

open CFSG.KC.Misc.GLM.Pf

theorem mcode_inj_proved : Function.Injective mcode := by
  intro A B h
  ext i j
  apply zb_inj
  rw [← mcode_bit, ← mcode_bit, h]

theorem mcode_add_proved (A B : Mat) : Nat.xor (mcode A) (mcode B) = mcode (A + B) := by
  apply Nat.eq_of_testBit_eq
  intro q
  change (mcode A ^^^ mcode B).testBit q = _
  rw [Nat.testBit_xor]
  by_cases hq : q < 25
  · have hi : q / 5 < 5 := by omega
    have hj : q % 5 < 5 := Nat.mod_lt _ (by decide)
    have e : q = 5 * (q / 5) + q % 5 := (Nat.div_add_mod q 5).symm
    have hA := mcode_bit A ⟨q / 5, hi⟩ ⟨q % 5, hj⟩
    have hB := mcode_bit B ⟨q / 5, hi⟩ ⟨q % 5, hj⟩
    have hAB := mcode_bit (A + B) ⟨q / 5, hi⟩ ⟨q % 5, hj⟩
    change (mcode A).testBit (5 * (q / 5) + q % 5) = _ at hA
    change (mcode B).testBit (5 * (q / 5) + q % 5) = _ at hB
    change (mcode (A + B)).testBit (5 * (q / 5) + q % 5) = _ at hAB
    rw [e, hA, hB, hAB, Matrix.add_apply, zb_add]
  · have hlt : ∀ X : Mat, (mcode X).testBit q = false := fun X =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (mcode_lt X)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, hlt, hlt]
    rfl

theorem mmulK_mcode_proved (A B : Mat) : mmulK (mcode A) (mcode B) = mcode (A * B) := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [mmulK_eq]
  have e : q = 5 * (q / 5) + q % 5 := (Nat.div_add_mod q 5).symm
  have hj : q % 5 < 5 := Nat.mod_lt _ (by decide)
  rw [e, mulR_bit _ _ _ _ hj]
  by_cases hq : q < 25
  · have hi : q / 5 < 5 := by omega
    rw [decide_eq_true hi, Bool.true_and]
    exact (sel_bit A B ⟨q / 5, hi⟩ ⟨q % 5, hj⟩).trans (mcode_bit (A * B) ⟨q / 5, hi⟩ ⟨q % 5, hj⟩).symm
  · rw [decide_eq_false (by omega), Bool.false_and, ← e,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (mcode_lt _)
        (Nat.pow_le_pow_right (by decide) (by omega)))]

end CFSG.KC.Misc.GLM

end
