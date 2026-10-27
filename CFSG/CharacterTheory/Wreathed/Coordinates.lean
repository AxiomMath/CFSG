module

public import CFSG.Open.LocalVocabulary

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

abbrev Wreath (m : ℕ) :=
  Multiplicative (ZMod m) ≀ᵣ Multiplicative (ZMod 2)

@[expose] def element (m : ℕ) (a b : ZMod m) (e : ZMod 2) : Wreath m :=
  ⟨fun q => Multiplicative.ofAdd (if Multiplicative.toAdd q = 0 then a else b),
    Multiplicative.ofAdd e⟩

@[simp] theorem element_left_zero (m : ℕ) (a b : ZMod m) (e : ZMod 2) :
    (element m a b e).left (Multiplicative.ofAdd 0) = Multiplicative.ofAdd a := by
  simp [element]

@[simp] theorem element_left_one (m : ℕ) (a b : ZMod m) (e : ZMod 2) :
    (element m a b e).left (Multiplicative.ofAdd 1) = Multiplicative.ofAdd b := by
  simp [element]

@[simp] theorem element_right (m : ℕ) (a b : ZMod m) (e : ZMod 2) :
    (element m a b e).right = Multiplicative.ofAdd e := rfl

theorem swap_exponent_cases (e : ZMod 2) : e = 0 ∨ e = 1 :=
  (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) e

theorem swap_coordinate_cases (q : Multiplicative (ZMod 2)) :
    q = Multiplicative.ofAdd 0 ∨ q = Multiplicative.ofAdd 1 := by
  rcases swap_exponent_cases (Multiplicative.toAdd q) with h | h
  · exact Or.inl (congrArg Multiplicative.ofAdd h)
  · exact Or.inr (congrArg Multiplicative.ofAdd h)

@[expose] def coordinateEquiv (m : ℕ) : Wreath m ≃ ZMod m × ZMod m × ZMod 2 where
  toFun g := (Multiplicative.toAdd (g.left (Multiplicative.ofAdd 0)),
    Multiplicative.toAdd (g.left (Multiplicative.ofAdd 1)), Multiplicative.toAdd g.right)
  invFun c := element m c.1 c.2.1 c.2.2
  left_inv g := by
    apply RegularWreathProduct.ext
    · funext q
      rcases swap_coordinate_cases q with rfl | rfl <;> simp [element]
    · rfl
  right_inv c := by
    rcases c with ⟨a, b, e⟩
    simp [element]

theorem element_injective (m : ℕ) :
    Function.Injective (fun c : ZMod m × ZMod m × ZMod 2 => element m c.1 c.2.1 c.2.2) :=
  (coordinateEquiv m).symm.injective

@[simp] theorem element_zero (m : ℕ) : element m 0 0 0 = 1 := by
  ext q <;> simp [element]

theorem element_base_mul (m : ℕ) (a b c d : ZMod m) (e : ZMod 2) :
    element m a b 0 * element m c d e = element m (a + c) (b + d) e := by
  apply RegularWreathProduct.ext
  · funext q
    apply Multiplicative.toAdd.injective
    change (if Multiplicative.toAdd q = 0 then a else b) +
      (if -(0 : ZMod 2) + Multiplicative.toAdd q = 0 then c else d) =
      if Multiplicative.toAdd q = 0 then a + c else b + d
    rw [show -(0 : ZMod 2) = 0 by decide, zero_add]
    split <;> rfl
  · simp [element]

theorem element_swap_mul (m : ℕ) (a b c d : ZMod m) (e : ZMod 2) :
    element m a b 1 * element m c d e = element m (a + d) (b + c) (1 + e) := by
  apply RegularWreathProduct.ext
  · funext q
    rcases swap_coordinate_cases q with rfl | rfl <;>
      simp [element, RegularWreathProduct.mul_def]
  · simp [element]

theorem element_base_pow (m : ℕ) (a b : ZMod m) (k : ℕ) :
    element m a b 0 ^ k = element m (k • a) (k • b) 0 := by
  induction k with
  | zero => simp
  | succ k hk =>
      rw [pow_succ, hk, element_base_mul]
      congr 1 <;> simp only [succ_nsmul, add_comm]

theorem element_swap_sq (m : ℕ) (a b : ZMod m) :
    element m a b 1 ^ 2 = element m (a + b) (a + b) 0 := by
  rw [pow_two, element_swap_mul]
  have htwo : (1 + 1 : ZMod 2) = 0 := by decide
  rw [htwo, add_comm b a]

theorem element_base_pow_modulus (m : ℕ) (a b : ZMod m) :
    element m a b 0 ^ m = 1 := by
  rw [element_base_pow]
  simp [nsmul_eq_mul]

theorem element_pow_twice_modulus (m : ℕ) (g : Wreath m) : g ^ (2 * m) = 1 := by
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m a b e ^ (2 * m) = 1
  rcases swap_exponent_cases e with rfl | rfl
  · rw [Nat.mul_comm 2 m, pow_mul, element_base_pow_modulus, one_pow]
  · rw [pow_mul, element_swap_sq, element_base_pow_modulus]

theorem card_wreath (m : ℕ) : Nat.card (Wreath m) = 2 * m ^ 2 := by
  rw [RegularWreathProduct.card]
  simp only [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  omega

end CFSG.Wreathed
