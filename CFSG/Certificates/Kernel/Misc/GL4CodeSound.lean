module

public import Certificates.Data.Kernel.Misc.GL4Code
public import Certificates.Data.A5GL42
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Certificates.Kernel.Misc.GL52MatProved

public section

namespace CFSG.KC.Misc.GL4

open CFSG.KC.Misc.Clos CFSG.KC.Misc.GLM.Pf
open Certificates.A5GL42 (Mat4 ofCode)

@[expose] def code4 (A : Mat4) : ℕ := ∑ i : Fin 4, ∑ j : Fin 4, (A i j).val * 2 ^ (4 * (i : ℕ) + j)

@[expose] def enc4 (g : GL (Fin 4) (ZMod 2)) : ℕ := code4 (g : Mat4)

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Misc.letN y k = k y := by
  cases y <;> rfl

theorem code4_eq (A : Mat4) : code4 A =
    ∑ i : Fin 4, (∑ j : Fin 4, (A i j).val * 2 ^ (1 * (j : ℕ))) * 2 ^ (4 * (i : ℕ)) := by
  unfold code4
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.one_mul, Nat.pow_add]
  ring

theorem row4_lt (A : Mat4) (i : Fin 4) :
    (∑ j : Fin 4, (A i j).val * 2 ^ (1 * (j : ℕ))) < 2 ^ 4 :=
  (pack_spec 1 4 _ (fun j => ZMod.val_lt (A i j))).1

theorem code4_lt (A : Mat4) : code4 A < 65536 := by
  rw [code4_eq]
  exact (pack_spec 4 4 _ (row4_lt A)).1

theorem code4_bit (A : Mat4) (i j : Fin 4) : (code4 A).testBit (4 * i + j) = zb (A i j) := by
  rw [code4_eq, (pack_spec 4 4 _ (row4_lt A)).2 i j j.isLt]
  have h := (pack_spec 1 4 _ (fun j => ZMod.val_lt (A i j))).2 j 0 (by decide)
  have e : (j : ℕ) = 1 * j + 0 := by omega
  rw [e]
  exact h

theorem zb_ofCode (c : ℕ) (i j : Fin 4) : zb (ofCode c i j) = c.testBit (4 * i + j) := by
  change zb (if c.testBit (4 * i.val + j.val) then 1 else 0) = _
  cases c.testBit (4 * i.val + j.val) <;> rfl

theorem ofCode_code4 (A : Mat4) : ofCode (code4 A) = A := by
  ext i j
  apply zb_inj
  rw [zb_ofCode, code4_bit]

theorem testBit_ge16 {c q : ℕ} (hc : c < 65536) (hq : 16 ≤ q) : c.testBit q = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc
    (by simpa using (Nat.pow_le_pow_right (by norm_num) hq : 2 ^ 16 ≤ 2 ^ q)))

theorem code4_ofCode {c : ℕ} (hc : c < 65536) : code4 (ofCode c) = c := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : q < 16
  · have e : q = 4 * (q / 4) + q % 4 := (Nat.div_add_mod q 4).symm
    have h := code4_bit (ofCode c) ⟨q / 4, by omega⟩ ⟨q % 4, by omega⟩
    rw [zb_ofCode] at h
    change (code4 (ofCode c)).testBit (4 * (q / 4) + q % 4) = c.testBit (4 * (q / 4) + q % 4) at h
    rw [e]
    exact h
  · rw [testBit_ge16 (code4_lt _) (by omega), testBit_ge16 hc (by omega)]

theorem ofCode_inj {a b : ℕ} (ha : a < 65536) (hb : b < 65536) (h : ofCode a = ofCode b) :
    a = b := by
  rw [← code4_ofCode ha, ← code4_ofCode hb, h]

@[expose] def term4 (a b k : ℕ) : ℕ :=
  ((a >>> k) &&& 4369) * 15 &&& ((b >>> (4 * k)) &&& 15) * 4369

theorem mul4F_eq (a b : ℕ) :
    mul4F a b = term4 a b 0 ^^^ term4 a b 1 ^^^ term4 a b 2 ^^^ term4 a b 3 := by
  unfold mul4F
  rw [letN_eq, letN_eq]
  rfl

theorem bit4369 : ∀ i < 4, ∀ j < 4, (4369 : ℕ).testBit (4 * i + j) = decide (j = 0) := by
  decide

theorem toNat_bit : ∀ b : Bool, ∀ j < 4, b.toNat.testBit j = (b && decide (j = 0)) := by
  decide

theorem toNat15_bit : ∀ b : Bool, ∀ j < 4, (b.toNat * 15).testBit j = b := by
  decide

theorem toNat15_lt (b : Bool) : b.toNat * 15 < 2 ^ 4 := by
  cases b <;> decide

theorem land4369 (x : ℕ) :
    x &&& 4369 = ∑ i : Fin 4, (x.testBit (4 * (i : ℕ))).toNat * 2 ^ (4 * (i : ℕ)) := by
  have hf : ∀ i : Fin 4, (x.testBit (4 * (i : ℕ))).toNat < 2 ^ 4 := fun i => by
    cases x.testBit (4 * (i : ℕ)) <;> decide
  obtain ⟨hlt, hbit⟩ := pack_spec 4 4 (fun i : Fin 4 => (x.testBit (4 * (i : ℕ))).toNat) hf
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_and]
  by_cases hq : q < 16
  · have e : q = 4 * (q / 4) + q % 4 := (Nat.div_add_mod q 4).symm
    have hj : q % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [e, hbit ⟨q / 4, by omega⟩ (q % 4) hj, bit4369 _ (by omega) _ hj, toNat_bit _ _ hj]
    change (x.testBit (4 * (q / 4) + q % 4) && _) = (x.testBit (4 * (q / 4)) && _)
    by_cases h0 : q % 4 = 0
    · rw [h0]
      rfl
    · simp [h0]
  · rw [testBit_ge16 (c := 4369) (by norm_num) (by omega), Bool.and_false,
      testBit_ge16 (by simpa using hlt) (by omega)]

theorem spread_eq (a k : ℕ) : ((a >>> k) &&& 4369) * 15 =
    ∑ i : Fin 4, (a.testBit (4 * (i : ℕ) + k)).toNat * 15 * 2 ^ (4 * (i : ℕ)) := by
  rw [land4369, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_shiftRight, Nat.add_comm k]
  ring

theorem copy_eq (b k : ℕ) : ((b >>> (4 * k)) &&& 15) * 4369 =
    ∑ _i : Fin 4, ((b >>> (4 * k)) &&& 15) * 2 ^ (4 * (_i : ℕ)) := by
  rw [Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
  norm_num
  ring

theorem term4_lt (a b k : ℕ) : term4 a b k < 2 ^ 16 := by
  unfold term4
  refine lt_of_le_of_lt Nat.and_le_left ?_
  rw [spread_eq]
  exact (pack_spec 4 4 _ fun i => toNat15_lt _).1

theorem term4_bit (a b k : ℕ) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    (term4 a b k).testBit (4 * i + j) = (a.testBit (4 * i + k) && b.testBit (4 * k + j)) := by
  have h15 : ∀ x : ℕ, x &&& 15 = x % 2 ^ 4 := fun x => Nat.and_two_pow_sub_one_eq_mod x 4
  have hlt : (b >>> (4 * k)) &&& 15 < 2 ^ 4 := by
    rw [h15]
    exact Nat.mod_lt _ (by norm_num)
  unfold term4
  rw [Nat.testBit_and, spread_eq, copy_eq,
    (pack_spec 4 4 _ fun i => toNat15_lt _).2 ⟨i, hi⟩ j hj,
    (pack_spec 4 4 (fun _ => (b >>> (4 * k)) &&& 15) fun _ => hlt).2 ⟨i, hi⟩ j hj,
    toNat15_bit _ _ hj, h15, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    decide_eq_true hj, Bool.true_and]

theorem mul4F_bit (a b : ℕ) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    (mul4F a b).testBit (4 * i + j) =
      ((((a.testBit (4 * i + 0) && b.testBit (4 * 0 + j)) ^^
        (a.testBit (4 * i + 1) && b.testBit (4 * 1 + j))) ^^
        (a.testBit (4 * i + 2) && b.testBit (4 * 2 + j))) ^^
        (a.testBit (4 * i + 3) && b.testBit (4 * 3 + j))) := by
  rw [mul4F_eq, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, term4_bit _ _ _ hi hj,
    term4_bit _ _ _ hi hj, term4_bit _ _ _ hi hj, term4_bit _ _ _ hi hj]

theorem mul4F_lt (a b : ℕ) : mul4F a b < 65536 := by
  rw [mul4F_eq]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (term4_lt _ _ _)
    (term4_lt _ _ _)) (term4_lt _ _ _)) (term4_lt _ _ _)

theorem mul4F_ofCode (a b : ℕ) : ofCode (mul4F a b) = ofCode a * ofCode b := by
  ext i j
  apply zb_inj
  rw [zb_ofCode, mul4F_bit _ _ i.isLt j.isLt, Matrix.mul_apply, Fin.sum_univ_four, zb_add, zb_add,
    zb_add, zb_mul, zb_mul, zb_mul, zb_mul, zb_ofCode, zb_ofCode, zb_ofCode, zb_ofCode, zb_ofCode,
    zb_ofCode, zb_ofCode, zb_ofCode]
  rfl

theorem code4_mul (A B : Mat4) : code4 (A * B) = mul4F (code4 A) (code4 B) := by
  have h := code4_ofCode (mul4F_lt (code4 A) (code4 B))
  rw [mul4F_ofCode, ofCode_code4, ofCode_code4] at h
  exact h

theorem ofCode_id4 : ofCode id4 = 1 := by
  decide

theorem code4_one : code4 1 = id4 := by
  rw [← ofCode_id4, code4_ofCode (by decide)]

theorem gl4_enc : ClosEnc enc4 mul4F id4 where
  enc_one := code4_one
  enc_mul a b := by
    change code4 ((a * b : GL (Fin 4) (ZMod 2)) : Mat4) = _
    rw [Units.val_mul, code4_mul]
    rfl
  inj a b h := by
    apply Units.val_injective
    rw [← ofCode_code4 (a : Mat4), ← ofCode_code4 (b : Mat4)]
    exact congrArg ofCode h

theorem enc4_lt (g : GL (Fin 4) (ZMod 2)) : enc4 g < 65536 := code4_lt _

theorem ofCode_enc4 (g : GL (Fin 4) (ZMod 2)) : ofCode (enc4 g) = g := ofCode_code4 _

end CFSG.KC.Misc.GL4

end
