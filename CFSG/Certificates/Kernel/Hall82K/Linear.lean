module

public import Certificates.Data.Kernel.Hall82K.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStab

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa

@[expose] def enc6 (a0 a1 a2 a3 a4 a5 : ℕ) : ℕ :=
  a0 + 64 * (a1 + 64 * (a2 + 64 * (a3 + 64 * (a4 + 64 * a5))))

@[expose] def codeL (f : Fin 64 → Fin 64) : ℕ :=
  enc6 (f 1).val (f 2).val (f 4).val (f 8).val (f 16).val (f 32).val

theorem fld_eq (c s : ℕ) : fld c s = c / 2 ^ s % 64 := by
  change (c >>> s) &&& 63 = _
  have h63 : (63 : ℕ) = 2 ^ 6 - 1 := rfl
  rw [Nat.shiftRight_eq_div_pow, h63, Nat.and_two_pow_sub_one_eq_mod]

theorem fld_digit_zero {a : ℕ} (ha : a < 64) (X : ℕ) : fld (a + 64 * X) 0 = a := by
  rw [fld_eq, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem fld_lt {a : ℕ} (ha : a < 64) : fld a 0 = a := by
  rw [fld_eq, pow_zero, Nat.div_one, Nat.mod_eq_of_lt ha]

theorem fld_digit_succ {a : ℕ} (ha : a < 64) (X s : ℕ) : fld (a + 64 * X) (s + 6) = fld X s := by
  rw [fld_eq, fld_eq, pow_add, mul_comm (2 ^ s), ← Nat.div_div_eq_div_mul]
  congr 2
  rw [show (2 : ℕ) ^ 6 = 64 by norm_num, Nat.add_mul_div_left _ _ (by norm_num : 0 < 64),
    Nat.div_eq_of_lt ha, zero_add]

theorem bitN_mul (v j a : ℕ) : Nat.mul (bitN v j) a = if v.testBit j then a else 0 := by
  have h : bitN v j = v / 2 ^ j % 2 := by
    change (v >>> j) &&& 1 = _
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.and_one_is_mod _
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h0 | h1
  · simp [h0]
  · simp [h1]

theorem ite_xor_eq (b : Bool) (acc a : ℕ) :
    (if b then acc ^^^ a else acc) = acc ^^^ (if b then a else 0) := by
  cases b <;> simp

theorem apL_enc6 {a0 a1 a2 a3 a4 a5 : ℕ} (h0 : a0 < 64) (h1 : a1 < 64) (h2 : a2 < 64)
    (h3 : a3 < 64) (h4 : a4 < 64) (h5 : a5 < 64) (v : ℕ) :
    apL (enc6 a0 a1 a2 a3 a4 a5) v = linV [a0, a1, a2, a3, a4, a5] v := by
  have e0 : fld (enc6 a0 a1 a2 a3 a4 a5) 0 = a0 := fld_digit_zero h0 _
  have e1 : fld (enc6 a0 a1 a2 a3 a4 a5) 6 = a1 := by
    rw [enc6, fld_digit_succ h0 _ 0, fld_digit_zero h1]
  have e2 : fld (enc6 a0 a1 a2 a3 a4 a5) 12 = a2 := by
    rw [enc6, fld_digit_succ h0 _ 6, fld_digit_succ h1 _ 0, fld_digit_zero h2]
  have e3 : fld (enc6 a0 a1 a2 a3 a4 a5) 18 = a3 := by
    rw [enc6, fld_digit_succ h0 _ 12, fld_digit_succ h1 _ 6, fld_digit_succ h2 _ 0,
      fld_digit_zero h3]
  have e4 : fld (enc6 a0 a1 a2 a3 a4 a5) 24 = a4 := by
    rw [enc6, fld_digit_succ h0 _ 18, fld_digit_succ h1 _ 12, fld_digit_succ h2 _ 6,
      fld_digit_succ h3 _ 0, fld_digit_zero h4]
  have e5 : fld (enc6 a0 a1 a2 a3 a4 a5) 30 = a5 := by
    rw [enc6, fld_digit_succ h0 _ 24, fld_digit_succ h1 _ 18, fld_digit_succ h2 _ 12,
      fld_digit_succ h3 _ 6, fld_digit_succ h4 _ 0, fld_lt h5]
  have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  unfold apL linV
  rw [e0, e1, e2, e3, e4, e5, hr]
  have hx : ∀ a b : ℕ, Nat.xor a b = a ^^^ b := fun _ _ => rfl
  simp only [bitN_mul, List.foldl_cons, List.foldl_nil, ite_xor_eq, Nat.zero_xor, hx,
    Nat.xor_assoc]
  simp

theorem fld_enc6 {a0 a1 a2 a3 a4 a5 : ℕ} (h0 : a0 < 64) (h1 : a1 < 64) (h2 : a2 < 64)
    (h3 : a3 < 64) (h4 : a4 < 64) (h5 : a5 < 64) :
    fld (enc6 a0 a1 a2 a3 a4 a5) 0 = a0 ∧ fld (enc6 a0 a1 a2 a3 a4 a5) 6 = a1 ∧
      fld (enc6 a0 a1 a2 a3 a4 a5) 12 = a2 ∧ fld (enc6 a0 a1 a2 a3 a4 a5) 18 = a3 ∧
      fld (enc6 a0 a1 a2 a3 a4 a5) 24 = a4 ∧ fld (enc6 a0 a1 a2 a3 a4 a5) 30 = a5 := by
  refine ⟨fld_digit_zero h0 _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [enc6, fld_digit_succ h0 _ 0, fld_digit_zero h1]
  · rw [enc6, fld_digit_succ h0 _ 6, fld_digit_succ h1 _ 0, fld_digit_zero h2]
  · rw [enc6, fld_digit_succ h0 _ 12, fld_digit_succ h1 _ 6, fld_digit_succ h2 _ 0,
      fld_digit_zero h3]
  · rw [enc6, fld_digit_succ h0 _ 18, fld_digit_succ h1 _ 12, fld_digit_succ h2 _ 6,
      fld_digit_succ h3 _ 0, fld_digit_zero h4]
  · rw [enc6, fld_digit_succ h0 _ 24, fld_digit_succ h1 _ 18, fld_digit_succ h2 _ 12,
      fld_digit_succ h3 _ 6, fld_digit_succ h4 _ 0, fld_lt h5]

theorem add_mul64_eq_or {a : ℕ} (ha : a < 64) (r : ℕ) : a + 64 * r = r <<< 6 ||| a := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by norm_num; omega : a < 2 ^ 6), Nat.shiftLeft_eq]
  ring

theorem lorTree_eq_enc6 {x0 x1 x2 x3 x4 x5 : ℕ} (h0 : x0 < 64) (h1 : x1 < 64) (h2 : x2 < 64)
    (h3 : x3 < 64) (h4 : x4 < 64) :
    ((x0 ||| x1 <<< 6) ||| (x2 <<< 12 ||| x3 <<< 18)) ||| (x4 <<< 24 ||| x5 <<< 30) =
      enc6 x0 x1 x2 x3 x4 x5 := by
  rw [enc6, add_mul64_eq_or h4, add_mul64_eq_or h3, add_mul64_eq_or h2, add_mul64_eq_or h1,
    add_mul64_eq_or h0]
  have hss : ∀ a m n : ℕ, a <<< m <<< n = a <<< (m + n) := fun a m n =>
    (Nat.shiftLeft_add a m n).symm
  rw [Nat.shiftLeft_or_distrib, Nat.shiftLeft_or_distrib, Nat.shiftLeft_or_distrib,
    Nat.shiftLeft_or_distrib, Nat.shiftLeft_or_distrib, Nat.shiftLeft_or_distrib,
    Nat.shiftLeft_or_distrib, Nat.shiftLeft_or_distrib, Nat.shiftLeft_or_distrib,
    Nat.shiftLeft_or_distrib]
  rw [hss x5, hss x5, hss x5, hss x5, hss x4, hss x4, hss x4, hss x3, hss x3, hss x2]
  have hlc : ∀ a b c : ℕ, a ||| (b ||| c) = b ||| (a ||| c) := fun a b c => by
    rw [← Nat.or_assoc, Nat.or_comm a b, Nat.or_assoc]
  simp only [Nat.reduceAdd, Nat.or_assoc, Nat.or_comm, hlc]

theorem apL_codeL {f : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    (v : Fin 64) : apL (codeL f) v.val = (f v).val := by
  rw [val_eq_linV hf v, codeL]
  exact apL_enc6 (f 1).2 (f 2).2 (f 4).2 (f 8).2 (f 16).2 (f 32).2 v.val

theorem compL_codeL {f g : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w)) :
    compL (codeL f) (codeL g) = codeL (fun v => f (g v)) := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ :=
    fld_enc6 (g 1).2 (g 2).2 (g 4).2 (g 8).2 (g 16).2 (g 32).2
  have hg : codeL g = enc6 (g 1).val (g 2).val (g 4).val (g 8).val (g 16).val (g 32).val := rfl
  unfold compL
  rw [hg, e0, e1, e2, e3, e4, e5, apL_codeL hf, apL_codeL hf, apL_codeL hf,
    apL_codeL hf, apL_codeL hf, apL_codeL hf]
  exact lorTree_eq_enc6 (f (g 1)).2 (f (g 2)).2 (f (g 4)).2 (f (g 8)).2 (f (g 16)).2

end CFSG.KC.Hall82K
