module

public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.Semidihedral

open CFSG.Open

theorem exponent_cases (e : ZMod 2) : e = 0 ∨ e = 1 := by
  exact (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) e

@[simp] theorem toModel_element (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    toModel n hn (element n hn i e) = modelElement n hn i e := by
  exact (presentationEquivModel n hn).apply_symm_apply _

@[simp] theorem element_eq_iff (n : ℕ) (hn : 3 ≤ n)
    (i j : ZMod (modulus n)) (e f : ZMod 2) :
    element n hn i e = element n hn j f ↔ i = j ∧ e = f := by
  constructor
  · intro h
    have hc := congrArg (coordinateEquiv n hn) h
    simpa only [coordinateEquiv_element, Prod.mk.injEq] using hc
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem element_zero_zero (n : ℕ) (hn : 3 ≤ n) :
    element n hn 0 0 = 1 := by
  simp [element_eq]

@[simp] theorem element_eq_one_iff (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    element n hn i e = 1 ↔ i = 0 ∧ e = 0 := by
  rw [← element_zero_zero n hn, element_eq_iff]

theorem element_rotation_mul (n : ℕ) (hn : 3 ≤ n)
    (i j : ZMod (modulus n)) (e : ZMod 2) :
    element n hn i 0 * element n hn j e = element n hn (i + j) e := by
  apply (presentationEquivModel n hn).injective
  change toModel n hn (element n hn i 0 * element n hn j e) =
    toModel n hn (element n hn (i + j) e)
  rw [map_mul, toModel_element, toModel_element, toModel_element]
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd i *
        action n hn (Multiplicative.ofAdd 0) (Multiplicative.ofAdd j) =
      Multiplicative.ofAdd (i + j)
    rw [action_zero]
    rfl
  · change Multiplicative.ofAdd (0 : ZMod 2) * Multiplicative.ofAdd e =
      Multiplicative.ofAdd e
    exact one_mul _

theorem element_reflection_mul (n : ℕ) (hn : 3 ≤ n)
    (i j : ZMod (modulus n)) (e : ZMod 2) :
    element n hn i 1 * element n hn j e =
      element n hn (i + twist n * j) (1 + e) := by
  apply (presentationEquivModel n hn).injective
  change toModel n hn (element n hn i 1 * element n hn j e) =
    toModel n hn (element n hn (i + twist n * j) (1 + e))
  rw [map_mul, toModel_element, toModel_element, toModel_element]
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd i *
        action n hn (Multiplicative.ofAdd 1) (Multiplicative.ofAdd j) =
      Multiplicative.ofAdd (i + twist n * j)
    rw [action_one]
    rfl
  · rfl

theorem element_rotation_pow (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (k : ℕ) :
    element n hn i 0 ^ k = element n hn (k • i) 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, element_rotation_mul, succ_nsmul]

theorem element_reflection_sq (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) :
    element n hn i 1 ^ 2 = element n hn ((half n : ZMod (modulus n)) * i) 0 := by
  rw [sq, element_reflection_mul, show (1 + 1 : ZMod 2) = 0 by decide]
  congr 1
  simp only [twist]
  ring

theorem r_pow_eq_element (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    r n ^ k = element n hn (k : ZMod (modulus n)) 0 := by
  apply (presentationEquivModel n hn).injective
  change toModel n hn (r n ^ k) = toModel n hn (element n hn (k : ZMod (modulus n)) 0)
  rw [map_pow, toModel_r, modelR_pow, toModel_element]

theorem s_eq_element (n : ℕ) (hn : 3 ≤ n) : s n = element n hn 0 1 := by
  apply (coordinateEquiv n hn).injective
  rw [coordinateEquiv_s, coordinateEquiv_element]

end CFSG.Semidihedral
