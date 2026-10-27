module

public import Certificates.Data.SmithD6Model
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

abbrev V := Fin 32 → ZMod 2

@[expose] def bit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bit_xor (a b : Bool) : bit (a ^^ b) = bit a + bit b := by
  cases a <;> cases b <;> decide

theorem bit_and (a b : Bool) : bit (a && b) = bit a * bit b := by
  cases a <;> cases b <;> decide

theorem bit_foldl (g : Nat → Bool) (n : Nat) :
    bit ((List.range n).foldl (fun acc k => acc ^^ g k) false) =
      ∑ k ∈ Finset.range n, bit (g k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil, bit_xor]

@[expose] def decode32 (c : Nat) : V := fun m => if c.testBit m.val then 1 else 0

theorem decode32_apply (c : Nat) (m : Fin 32) : decode32 c m = if c.testBit m.val then 1 else 0 :=
  rfl

theorem decode32_apply_bit (c : Nat) (m : Fin 32) : decode32 c m = bit (c.testBit m.val) := rfl

theorem decode32_xor (a b : Nat) : decode32 (a ^^^ b) = decode32 a + decode32 b := by
  funext m
  simp only [decode32_apply, Pi.add_apply, Nat.testBit_xor]
  cases a.testBit m.val <;> cases b.testBit m.val <;> decide

theorem decode32_zero : decode32 0 = 0 := by
  funext m
  simp [decode32_apply]

theorem decode32_two_pow (m : Fin 32) : decode32 (2 ^ m.val) = Pi.single m 1 := by
  funext i
  rw [decode32_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : i = m
  · subst h; simp
  · have : m.val ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [h, this]

theorem eq_of_decode32_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : decode32 a = decode32 b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · have := congrFun h ⟨i, hi⟩
    simp only [decode32_apply] at this
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem decode32_surj (v : V) : ∃ c < 2 ^ 32, decode32 c = v := by
  have hf : Function.Injective (fun n : Fin (2 ^ 32) => decode32 n.val) := by
    intro m n hmn
    exact Fin.ext (eq_of_decode32_eq m.isLt n.isLt hmn)
  have hcard : Fintype.card (Fin (2 ^ 32)) = Fintype.card V := by
    simp [Fintype.card_fun, ZMod.card]
  obtain ⟨n, hn⟩ := ((Fintype.bijective_iff_injective_and_card
    (fun n : Fin (2 ^ 32) => decode32 n.val)).2 ⟨hf, hcard⟩).2 v
  exact ⟨n.val, n.isLt, hn⟩

@[expose] noncomputable def code32 (v : V) : ℕ := Classical.choose (decode32_surj v)

theorem code32_lt (v : V) : code32 v < 2 ^ 32 := (Classical.choose_spec (decode32_surj v)).1

theorem decode32_code32 (v : V) : decode32 (code32 v) = v :=
  (Classical.choose_spec (decode32_surj v)).2

theorem code32_decode32 {c : ℕ} (hc : c < 2 ^ 32) : code32 (decode32 c) = c :=
  eq_of_decode32_eq (code32_lt _) hc (decode32_code32 _)

@[expose] noncomputable def colsLin (cols : Array Nat) : V →ₗ[ZMod 2] V :=
  ∑ m : Fin 32, (LinearMap.proj m : V →ₗ[ZMod 2] ZMod 2).smulRight (decode32 cols[m.val]!)

theorem colsLin_apply (cols : Array Nat) (v : V) :
    colsLin cols v = ∑ m : Fin 32, v m • decode32 cols[m.val]! := by
  simp [colsLin, LinearMap.sum_apply]

theorem colsLin_single (cols : Array Nat) (m : Fin 32) :
    colsLin cols (Pi.single m 1) = decode32 cols[m.val]! := by
  rw [colsLin_apply, Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem decode32_foldl (cols : Array Nat) (c : Nat) (n : Nat) :
    decode32 ((List.range n).foldl (fun acc m => if c.testBit m then acc ^^^ cols[m]! else acc) 0) =
      ∑ m ∈ Finset.range n, if c.testBit m then decode32 cols[m]! else 0 := by
  induction n with
  | zero => simp [decode32_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs
    · rw [decode32_xor]
    · rw [add_zero]

theorem decode32_applyCols {cols : Array Nat} (h : cols.size = 32) (c : Nat) :
    decode32 (applyCols cols c) = colsLin cols (decode32 c) := by
  unfold applyCols
  rw [h, decode32_foldl, colsLin_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun m => if c.testBit m then decode32 cols[m]! else 0) 32]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [decode32_apply]
  split_ifs <;> simp

theorem linearMap_ext_single {f g : V →ₗ[ZMod 2] V}
    (h : ∀ m : Fin 32, f (Pi.single m 1) = g (Pi.single m 1)) : f = g :=
  (Pi.basisFun (ZMod 2) (Fin 32)).ext fun m => by rw [Pi.basisFun_apply]; exact h m

theorem linearEquiv_ext_single {f g : V ≃ₗ[ZMod 2] V}
    (h : ∀ m : Fin 32, f (Pi.single m 1) = g (Pi.single m 1)) : f = g :=
  LinearEquiv.toLinearMap_injective (linearMap_ext_single h)

end CFSG.GF2Type.SmithTypeE.DMod
