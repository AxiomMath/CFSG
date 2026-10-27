module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Semidihedral

abbrev Cyclic (d : ℕ) := Multiplicative (ZMod d)

@[expose] def modulus (n : ℕ) : ℕ := 2 ^ (n - 1)

@[expose] def half (n : ℕ) : ℕ := 2 ^ (n - 2)

@[expose] def twist (n : ℕ) : ZMod (modulus n) := (half n : ZMod (modulus n)) - 1

theorem modulus_eq_two_mul_half {n : ℕ} (hn : 2 ≤ n) :
    modulus n = 2 * half n := by
  have he : n - 1 = (n - 2) + 1 := by omega
  simp only [modulus, half, he, pow_succ]
  omega

theorem half_even {n : ℕ} (hn : 3 ≤ n) : Even (half n) := by
  have he : n - 2 = (n - 3) + 1 := by omega
  rw [half, he, pow_succ]
  exact ⟨2 ^ (n - 3), by omega⟩

theorem twist_sq {n : ℕ} (hn : 3 ≤ n) : twist n ^ 2 = 1 := by
  have hmod : (modulus n : ZMod (modulus n)) = 0 := ZMod.natCast_self _
  have hdouble : 2 * (half n : ZMod (modulus n)) = 0 := by
    calc
      2 * (half n : ZMod (modulus n)) = ((2 * half n : ℕ) : ZMod (modulus n)) := by
        push_cast
        rfl
      _ = (modulus n : ZMod (modulus n)) :=
        congrArg (fun d : ℕ => (d : ZMod (modulus n))) (modulus_eq_two_mul_half (by omega)).symm
      _ = 0 := hmod
  obtain ⟨k, hk⟩ := half_even hn
  have hsq : (half n : ZMod (modulus n)) ^ 2 = 0 := by
    calc
      (half n : ZMod (modulus n)) ^ 2 =
          (2 * (half n : ZMod (modulus n))) * (k : ZMod (modulus n)) := by
        have hk' : (half n : ZMod (modulus n)) = 2 * (k : ZMod (modulus n)) := by
          rw [hk]
          push_cast
          ring
        rw [hk']
        ring
      _ = 0 := by rw [hdouble, zero_mul]
  unfold twist
  calc
    ((half n : ZMod (modulus n)) - 1) ^ 2 =
        (half n : ZMod (modulus n)) ^ 2 - 2 * (half n : ZMod (modulus n)) + 1 := by ring
    _ = 1 := by rw [hsq, hdouble]; ring

theorem twist_eq_natCast {n : ℕ} :
    twist n = ((2 ^ (n - 2) - 1 : ℕ) : ZMod (modulus n)) := by
  have hpositive : 1 ≤ 2 ^ (n - 2) := Nat.succ_le_of_lt (pow_pos (by decide) _)
  simp only [twist, half, Nat.cast_sub hpositive, Nat.cast_one]

@[expose] def twistAut (n : ℕ) (hn : 3 ≤ n) : MulAut (Cyclic (modulus n)) where
  toFun x := Multiplicative.ofAdd (twist n * Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (twist n * Multiplicative.toAdd x)
  left_inv x := by
    apply Multiplicative.toAdd.injective
    change twist n * (twist n * Multiplicative.toAdd x) = Multiplicative.toAdd x
    rw [← mul_assoc, ← sq, twist_sq hn, one_mul]
  right_inv x := by
    apply Multiplicative.toAdd.injective
    change twist n * (twist n * Multiplicative.toAdd x) = Multiplicative.toAdd x
    rw [← mul_assoc, ← sq, twist_sq hn, one_mul]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    exact mul_add _ _ _

theorem twistAut_sq (n : ℕ) (hn : 3 ≤ n) : twistAut n hn ^ 2 = 1 := by
  ext x
  apply Multiplicative.toAdd.injective
  change twist n * (twist n * Multiplicative.toAdd x) = Multiplicative.toAdd x
  rw [← mul_assoc, ← sq, twist_sq hn, one_mul]

@[expose] def action (n : ℕ) (hn : 3 ≤ n) :
    Cyclic 2 →* MulAut (Cyclic (modulus n)) where
  toFun e := twistAut n hn ^ e.toAdd.val
  map_one' := by simp
  map_mul' e f := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_eq_pow_mod _ (twistAut_sq n hn), pow_add]

@[simp] theorem action_zero (n : ℕ) (hn : 3 ≤ n) :
    action n hn (Multiplicative.ofAdd 0) = 1 := by simp [action]

@[simp] theorem action_one (n : ℕ) (hn : 3 ≤ n) :
    action n hn (Multiplicative.ofAdd 1) = twistAut n hn := by
  simp [action, ZMod.val_one_eq_one_mod]

abbrev Model (n : ℕ) (hn : 3 ≤ n) :=
  Cyclic (modulus n) ⋊[action n hn] Cyclic 2

@[expose] def modelR (n : ℕ) (hn : 3 ≤ n) : Model n hn :=
  SemidirectProduct.inl (Multiplicative.ofAdd 1)

@[expose] def modelS (n : ℕ) (hn : 3 ≤ n) : Model n hn :=
  SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[expose] def modelElement (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) : Model n hn :=
  ⟨Multiplicative.ofAdd i, Multiplicative.ofAdd e⟩

theorem modelR_pow (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    modelR n hn ^ k = modelElement n hn (k : ZMod (modulus n)) 0 := by
  rw [modelR, ← map_pow]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change k • (1 : ZMod (modulus n)) = (k : ZMod (modulus n))
    simp
  · rfl

theorem modelS_pow (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    modelS n hn ^ k = modelElement n hn 0 (k : ZMod 2) := by
  rw [modelS, ← map_pow]
  apply SemidirectProduct.ext
  · rfl
  · apply Multiplicative.toAdd.injective
    change k • (1 : ZMod 2) = (k : ZMod 2)
    simp

theorem modelS_sq (n : ℕ) (hn : 3 ≤ n) : modelS n hn ^ 2 = 1 := by
  rw [modelS_pow]
  rfl

theorem modelR_modulus (n : ℕ) (hn : 3 ≤ n) :
    modelR n hn ^ modulus n = 1 := by
  rw [modelR_pow, ZMod.natCast_self]
  rfl

theorem modelS_conj_modelR (n : ℕ) (hn : 3 ≤ n) :
    modelS n hn * modelR n hn * (modelS n hn)⁻¹ =
      modelR n hn ^ (2 ^ (n - 2) - 1) := by
  rw [modelS, modelR, ← map_inv, ← SemidirectProduct.inl_aut, action_one, ← map_pow]
  apply SemidirectProduct.inl_injective.eq_iff.mpr
  apply Multiplicative.toAdd.injective
  change twist n * 1 = (2 ^ (n - 2) - 1) • (1 : ZMod (modulus n))
  simp [twist_eq_natCast]

end CFSG.Semidihedral
