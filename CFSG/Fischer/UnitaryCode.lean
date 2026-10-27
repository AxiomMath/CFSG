module

public import CFSG.Fischer.F4Code
public import Certificates.Data.CFSGNative.F4.Unitary
import all CFSG.Fischer.F4
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Fischer

open CFSG.F4.Native

theorem foldl_add_six (f : ℕ → ℕ) :
    (List.range 6).foldl (fun acc i => acc + f i) 0 = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [List.range_succ]

theorem codeOf_eq_digits (w : Fin 6 → F4) :
    codeOf w = (w 0).code.val * 4 ^ 0 + (w 1).code.val * 4 ^ 1 + (w 2).code.val * 4 ^ 2 +
      (w 3).code.val * 4 ^ 3 + (w 4).code.val * 4 ^ 4 + (w 5).code.val * 4 ^ 5 := by
  unfold codeOf; ring

theorem scaleC_codeOf (a : F4) (w : Fin 6 → F4) :
    scaleC a.code.val (codeOf w) = codeOf (a • w) := by
  unfold scaleC
  rw [foldl_add_six, codeOf_eq_digits (a • w)]
  have hw : ∀ k : Fin 6, coord (codeOf w) k.val = (w k).code.val := coord_codeOf w
  have e : ∀ k : Fin 6, f4mul a.code.val (coord (codeOf w) k.val) = ((a • w) k).code.val := by
    intro k
    rw [hw, Pi.smul_apply, smul_eq_mul, code_mul]
  have e0 : f4mul a.code.val (coord (codeOf w) 0) = ((a • w) 0).code.val := e 0
  have e1 : f4mul a.code.val (coord (codeOf w) 1) = ((a • w) 1).code.val := e 1
  have e2 : f4mul a.code.val (coord (codeOf w) 2) = ((a • w) 2).code.val := e 2
  have e3 : f4mul a.code.val (coord (codeOf w) 3) = ((a • w) 3).code.val := e 3
  have e4 : f4mul a.code.val (coord (codeOf w) 4) = ((a • w) 4).code.val := e 4
  have e5 : f4mul a.code.val (coord (codeOf w) 5) = ((a • w) 5).code.val := e 5
  rw [e0, e1, e2, e3, e4, e5]

theorem xor_digit (x1 x2 y1 y2 : ℕ) (h1 : x1 < 4) (h2 : x2 < 4) :
    (x1 + 4 * y1) ^^^ (x2 + 4 * y2) = (x1 ^^^ x2) + 4 * (y1 ^^^ y2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  have hx : x1 ^^^ x2 < 2 ^ 2 := Nat.xor_lt_two_pow (by omega) (by omega)
  rw [Nat.testBit_xor, h4, add_comm x1, add_comm x2, add_comm (x1 ^^^ x2),
    Nat.testBit_two_pow_mul_add _ (by omega), Nat.testBit_two_pow_mul_add _ (by omega),
    Nat.testBit_two_pow_mul_add _ hx]
  split_ifs <;> simp [Nat.testBit_xor]

theorem codeOf_nested (w : Fin 6 → F4) :
    codeOf w = (w 0).code.val + 4 * ((w 1).code.val + 4 * ((w 2).code.val + 4 * ((w 3).code.val +
      4 * ((w 4).code.val + 4 * (w 5).code.val)))) := by
  unfold codeOf; ring

theorem codeOf_add (a b : Fin 6 → F4) : codeOf (a + b) = codeOf a ^^^ codeOf b := by
  have l := fun x : F4 => code_lt x
  rw [codeOf_nested, codeOf_nested a, codeOf_nested b]
  simp only [Pi.add_apply, code_add]
  rw [xor_digit _ _ _ _ (l _) (l _), xor_digit _ _ _ _ (l _) (l _),
    xor_digit _ _ _ _ (l _) (l _), xor_digit _ _ _ _ (l _) (l _),
    xor_digit _ _ _ _ (l _) (l _)]

theorem code_eq_zero_iff (x : F4) : x.code.val = 0 ↔ x = 0 := by
  revert x; decide

@[expose] def lead (w : Fin 6 → F4) : F4 :=
  if w 0 ≠ 0 then w 0 else if w 1 ≠ 0 then w 1 else if w 2 ≠ 0 then w 2 else
    if w 3 ≠ 0 then w 3 else if w 4 ≠ 0 then w 4 else w 5

theorem leadC_codeOf (w : Fin 6 → F4) : leadC (codeOf w) = (lead w).code.val := by
  have hw : ∀ k : Fin 6, coord (codeOf w) k.val = (w k).code.val := coord_codeOf w
  have e0 : coord (codeOf w) 0 = (w 0).code.val := hw 0
  have e1 : coord (codeOf w) 1 = (w 1).code.val := hw 1
  have e2 : coord (codeOf w) 2 = (w 2).code.val := hw 2
  have e3 : coord (codeOf w) 3 = (w 3).code.val := hw 3
  have e4 : coord (codeOf w) 4 = (w 4).code.val := hw 4
  have e5 : coord (codeOf w) 5 = (w 5).code.val := hw 5
  unfold leadC lead
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldr_append,
    List.foldr_cons, List.foldr_nil, e0, e1, e2, e3, e4, e5, bne_iff_ne, ne_eq,
    code_eq_zero_iff]
  split_ifs <;> (simp_all; try rfl)

@[expose] def normV (w : Fin 6 → F4) : Fin 6 → F4 := (lead w * lead w) • w

theorem normC_codeOf (w : Fin 6 → F4) : normC (codeOf w) = codeOf (normV w) := by
  unfold normC normV
  simp only
  rw [leadC_codeOf, ← code_mul, scaleC_codeOf]

theorem tvC_codeOf (v x : Fin 6 → F4) :
    tvC (codeOf v) (codeOf x) = codeOf (x + hermStd x v • v) := by
  unfold tvC addC
  rw [hermC_codeOf, scaleC_codeOf, codeOf_add]

end CFSG.Fischer
