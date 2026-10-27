module

public import Mathlib.Data.Fintype.Prod

public section

namespace CFSG.EvenSporadicStandard.M11Std

abbrev SMod : Type := Fin 2 × Fin 2 × Fin 8

namespace SMod

@[expose] def three (i : Fin 2) : Fin 8 := if i = 0 then 1 else 3

@[expose] def mul (x y : SMod) : SMod := (x.1 + y.1, x.2.1 + y.2.1, x.2.2 * three y.2.1 + y.2.2)

@[expose] def inv (x : SMod) : SMod := (x.1, x.2.1, -(x.2.2 * three x.2.1))

@[expose] def one : SMod := (0, 0, 0)

@[expose] def tt : SMod := (1, 0, 0)

@[expose] def bb : SMod := (0, 1, 0)

@[expose] def aa : SMod := (0, 0, 1)

@[expose] def zz : SMod := (0, 0, 4)

@[expose] def IsCentral (x : SMod) : Prop := ∀ y, mul x y = mul y x

instance : DecidablePred IsCentral := fun x => by unfold IsCentral; infer_instance

@[expose] def inW (x : SMod) : Prop := x.2.1 = 0 ∧ (x.2.2 = 0 ∨ x.2.2 = 4)

instance : DecidablePred inW := fun x => by unfold inW; infer_instance

@[expose] def inE1 (x : SMod) : Prop := x.2.2 = 0 ∨ x.2.2 = 4

instance : DecidablePred inE1 := fun x => by unfold inE1; infer_instance

@[expose] def inE2 (x : SMod) : Prop :=
  (x.2.1 = 0 ∧ (x.2.2 = 0 ∨ x.2.2 = 4)) ∨ (x.2.1 = 1 ∧ (x.2.2 = 2 ∨ x.2.2 = 6))

instance : DecidablePred inE2 := fun x => by unfold inE2; infer_instance

@[expose] def inH (x : SMod) : Prop := x.2.2.val % 2 = 0

instance : DecidablePred inH := fun x => by unfold inH; infer_instance

theorem inv_mul' : ∀ x : SMod, mul (inv x) x = one := by decide

theorem sq_fst : ∀ x : SMod, (mul x x).1 = 0 := by decide

theorem isCentral_iff : ∀ x : SMod, IsCentral x ↔ inW x := by decide

theorem exists_noncomm : ∀ x : SMod, mul x x = one → ¬ IsCentral x →
    ∃ y, mul x (mul (mul y x) (inv y)) ≠ mul (mul (mul y x) (inv y)) x := by decide

theorem noncentral_invol : ∀ x : SMod, mul x x = one → ¬ inW x → x.2.1 = 1 ∧ inH x := by decide

theorem inW_mul : ∀ x y : SMod, inW x → inW y → inW (mul x y) := by decide
theorem inW_inv : ∀ x : SMod, inW x → inW (inv x) := by decide
theorem inE1_mul : ∀ x y : SMod, inE1 x → inE1 y → inE1 (mul x y) := by decide
theorem inE1_inv : ∀ x : SMod, inE1 x → inE1 (inv x) := by decide
theorem inE2_mul : ∀ x y : SMod, inE2 x → inE2 y → inE2 (mul x y) := by decide
theorem inE2_inv : ∀ x : SMod, inE2 x → inE2 (inv x) := by decide
theorem inH_mul : ∀ x y : SMod, inH x → inH y → inH (mul x y) := by decide
theorem inH_inv : ∀ x : SMod, inH x → inH (inv x) := by decide

theorem inE1_sq : ∀ m : SMod, inE1 m → mul m m = one := by decide
theorem inE1_comm : ∀ m m' : SMod, inE1 m → inE1 m' → mul m m' = mul m' m := by decide
theorem orbit_cases : ∀ m : SMod, m.1 = 1 → inE1 m →
    m = (1, 0, 0) ∨ m = (1, 0, 4) ∨ m = (1, 1, 0) ∨ m = (1, 1, 4) := by decide
theorem inE1_or_inE2 : ∀ u : SMod, u.2.1 = 1 → inH u → inE1 u ∨ inE2 u := by decide
theorem mul_tt_comm : ∀ x : SMod, mul x tt = mul tt x := by decide
theorem inW_cases : ∀ w : SMod, inW w → w = one ∨ w = tt ∨ w = zz ∨ w = (1, 0, 4) := by decide
theorem inW_inE1 : ∀ x : SMod, inW x → inE1 x := by decide
theorem inW_inE2 : ∀ x : SMod, inW x → inE2 x := by decide

theorem inH_normalizes_E1 : ∀ m x : SMod, inH m → inE1 x → inE1 (mul (mul m x) (inv m)) := by
  decide

theorem conj_a_E2 : ∀ x : SMod, inE2 x → inE1 (mul (mul (inv aa) x) aa) := by decide

theorem card_inW : (Finset.univ.filter fun x : SMod => inW x).card = 4 := by decide
theorem card_inE1 : (Finset.univ.filter fun x : SMod => inE1 x).card = 8 := by decide
theorem card_inH : (Finset.univ.filter fun x : SMod => inH x).card = 16 := by decide

end SMod

end CFSG.EvenSporadicStandard.M11Std
