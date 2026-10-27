module

public import CFSG.LieType.Steinberg.Classical.SpinOdd.Basic
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Weyl
public import CFSG.LieType.Steinberg.PartB

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinOdd

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem

variable {n : ℕ} {K : Type} [Field K]

@[expose] def sgnAt (k m : Fin n) : ℤ := if m = k then -1 else 1

theorem sgnAt_eq_one_or_eq_neg_one (k m : Fin n) : sgnAt k m = 1 ∨ sgnAt k m = -1 := by
  unfold sgnAt
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem cast_sgnAt (k m : Fin n) : ((sgnAt k m : ℤ) : K) = longWeylSign k m := by
  unfold sgnAt longWeylSign
  split_ifs <;> simp

theorem longWeylBool_true_false' (i j m : Fin n) (r : Bool) :
    longWeylBool i j true false m r = r := by
  cases r <;> simp [longWeylBool]

theorem single_comp_swap' (a p q : Fin n) (x : ℤ) :
    Pi.single a x ∘ Equiv.swap p q = Pi.single (Equiv.swap p q a) x := by
  rw [Pi.single_comp_equiv, Equiv.symm_swap]

theorem sgn_mul_single (k i : Fin n) (s : Bool) (a : Fin n) :
    (if a = k then -1 else 1) * (Pi.single i (boolSign s) : Fin n → ℤ) a =
      (Pi.single i (boolSign (shortWeylBool k i s)) : Fin n → ℤ) a := by
  by_cases ha : a = i
  · subst ha
    by_cases hk : a = k
    · simp [shortWeylBool, hk]
    · simp [shortWeylBool, hk]
  · simp [ha]

theorem toStdB_reflection_long_of_lt {k : Fin n} (hk : k.val + 1 < n) {γ : Fin n → ℤ}
    {i j : Fin n} {s t : Bool}
    (h : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    toStdB n (reflection (cartanB n) k γ) =
      Pi.single (Equiv.swap k ⟨k.val + 1, hk⟩ i) (boolSign s) +
        Pi.single (Equiv.swap k ⟨k.val + 1, hk⟩ j) (boolSign t) := by
  rw [toStdB_reflection_of_lt n hk, h, Pi.add_comp, single_comp_swap', single_comp_swap']

theorem toStdB_reflection_short_of_lt {k : Fin n} (hk : k.val + 1 < n) {γ : Fin n → ℤ}
    {i : Fin n} {s : Bool} (h : toStdB n γ = Pi.single i (boolSign s)) :
    toStdB n (reflection (cartanB n) k γ) =
      Pi.single (Equiv.swap k ⟨k.val + 1, hk⟩ i) (boolSign s) := by
  rw [toStdB_reflection_of_lt n hk, h, single_comp_swap']

theorem toStdB_reflection_long_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) {γ : Fin n → ℤ}
    {i j : Fin n} {s t : Bool}
    (h : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    toStdB n (reflection (cartanB n) k γ) =
      Pi.single i (boolSign (shortWeylBool k i s)) +
        Pi.single j (boolSign (shortWeylBool k j t)) := by
  rw [toStdB_reflection, stdReflB_of_not_lt n hk, h]
  funext a
  rw [Pi.add_apply, mul_add, Pi.add_apply, sgn_mul_single, sgn_mul_single]

theorem toStdB_reflection_short_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) {γ : Fin n → ℤ}
    {i : Fin n} {s : Bool} (h : toStdB n γ = Pi.single i (boolSign s)) :
    toStdB n (reflection (cartanB n) k γ) = Pi.single i (boolSign (shortWeylBool k i s)) := by
  rw [toStdB_reflection, stdReflB_of_not_lt n hk, h]
  funext a
  rw [sgn_mul_single]

theorem weylB_conj_x (k : Fin n) {β : Fin n → ℤ} (hβ : β ∈ roots (isFiniteType_cartanB n) ∅) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ u : K,
      weylB K k * x n K β u * (weylB K k)⁻¹ =
        x n K (reflection (cartanB n) k β) ((ε : K) * u) := by
  rcases mem_roots_iff.mp hβ with ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · by_cases hk : k.val + 1 < n
    · set π := Equiv.swap k ⟨k.val + 1, hk⟩
      have hij' : π i ≠ π j := π.injective.ne hij
      refine ⟨repSign (π i) (π j) s t * repSign i j s t * sgnAt k i * sgnAt k j,
        sign_mul_sign_eq (sign_mul_sign_eq (sign_mul_sign_eq (repSign_eq_one_or_eq_neg_one _ _ _ _)
          (repSign_eq_one_or_eq_neg_one _ _ _ _)) (sgnAt_eq_one_or_eq_neg_one _ _))
          (sgnAt_eq_one_or_eq_neg_one _ _), fun u => ?_⟩
      rw [x_eq_long hij h, weylB_conj_longRoot_of_lt K hk hij, longWeylBool_true_false',
        longWeylBool_true_false', x_eq_long hij' (toStdB_reflection_long_of_lt hk h),
        ← cast_sgnAt, ← cast_sgnAt]
      congr 2
      push_cast
      have hr := repSign_cast_mul_self (K := K) (π i) (π j) s t
      linear_combination (-(repSign i j s t : K) * sgnAt k i * sgnAt k j * u) * hr
    · refine ⟨repSign i j (shortWeylBool k i s) (shortWeylBool k j t) * repSign i j s t *
        sgnAt k i * sgnAt k j,
        sign_mul_sign_eq (sign_mul_sign_eq (sign_mul_sign_eq (repSign_eq_one_or_eq_neg_one _ _ _ _)
          (repSign_eq_one_or_eq_neg_one _ _ _ _)) (sgnAt_eq_one_or_eq_neg_one _ _))
          (sgnAt_eq_one_or_eq_neg_one _ _), fun u => ?_⟩
      rw [x_eq_long hij h, weylB_conj_longRoot_of_not_lt K hk hij,
        x_eq_long hij (toStdB_reflection_long_of_not_lt hk h), ← cast_sgnAt, ← cast_sgnAt]
      congr 2
      push_cast
      have hr := repSign_cast_mul_self (K := K) i j (shortWeylBool k i s) (shortWeylBool k j t)
      linear_combination (-(repSign i j s t : K) * sgnAt k i * sgnAt k j * u) * hr
  · by_cases hk : k.val + 1 < n
    · refine ⟨sgnAt k i, sgnAt_eq_one_or_eq_neg_one _ _, fun u => ?_⟩
      rw [x_eq_short h, weylB_conj_shortRoot_of_lt K hk, longWeylBool_true_false',
        x_eq_short (toStdB_reflection_short_of_lt hk h), ← cast_sgnAt]
      congr 2
      ring
    · refine ⟨-(boolSign (shortWeylBool k i s) * sgnAt k i * boolSign s),
        by
          rcases sign_mul_sign_eq (sign_mul_sign_eq (boolSign_eq_one_or_eq_neg_one _)
            (sgnAt_eq_one_or_eq_neg_one k i)) (boolSign_eq_one_or_eq_neg_one s) with h' | h' <;>
            rw [h'] <;> simp, fun u => ?_⟩
      rw [x_eq_short h, weylB_conj_shortRoot_of_not_lt K hk,
        x_eq_short (toStdB_reflection_short_of_not_lt hk h), ← cast_sgnAt]
      congr 2
      push_cast
      have hs := intCast_mul_self_of_sq (K := K)
        (boolSign_eq_one_or_eq_neg_one (shortWeylBool k i s))
      linear_combination ((sgnAt k i : K) * boolSign s * u) * hs

theorem longCoroot_true_false {k k' : Fin n} (hkk' : k ≠ k') (m : Fin n) (r : Bool) :
    longCoroot k k' true false m r =
      (Pi.single m (boolSign r) : Fin n → ℤ) k - (Pi.single m (boolSign r) : Fin n → ℤ) k' := by
  unfold longCoroot
  by_cases hm : m = k
  · subst hm
    cases r <;> simp [Ne.symm hkk', hkk']
  · by_cases hm' : m = k'
    · subst hm'
      cases r <;> simp [hm, Ne.symm hm]
    · simp [hm, hm', Ne.symm hm, Ne.symm hm']

theorem shortCoroot_true (k m : Fin n) (r : Bool) :
    shortCoroot k true m r = 2 * (Pi.single m (boolSign r) : Fin n → ℤ) k := by
  unfold shortCoroot
  by_cases hm : m = k
  · subst hm
    cases r <;> simp
  · simp [hm, Ne.symm hm]

theorem torusB_conj_x (k : Fin n) (τ : Kˣ) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) (v : K) :
    torusB K k τ * x n K γ v * (torusB K k τ)⁻¹ =
      x n K γ (((τ ^ coroot (cartanB n) k γ : Kˣ) : K) * v) := by
  rcases mem_roots_iff.mp hγ with ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · by_cases hk : k.val + 1 < n
    · have hk1 : k ≠ (⟨k.val + 1, hk⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
      rw [torusB_of_lt K hk rfl hk1, x_eq_long hij h, HypFrame.longTorus_conj_longRoot,
        x_eq_long hij h, coroot_cartanB_of_lt n hk, h, longCoroot_true_false hk1,
        longCoroot_true_false hk1]
      congr 2
      simp only [Pi.add_apply]
      ring_nf
    · rw [torusB_of_not_lt K hk, x_eq_long hij h, OddFrame.shortTorus_conj_longRoot,
        x_eq_long hij h, coroot_cartanB_of_not_lt n hk, h, shortCoroot_true, shortCoroot_true]
      congr 2
      simp only [Pi.add_apply]
      ring_nf
  · by_cases hk : k.val + 1 < n
    · have hk1 : k ≠ (⟨k.val + 1, hk⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
      rw [torusB_of_lt K hk rfl hk1, x_eq_short h, OddFrame.longTorus_conj_shortRoot,
        x_eq_short h, coroot_cartanB_of_lt n hk, h, longCoroot_true_false hk1]
      congr 2
      ring
    · rw [torusB_of_not_lt K hk, x_eq_short h, OddFrame.shortTorus_conj_shortRoot,
        x_eq_short h, coroot_cartanB_of_not_lt n hk, h, shortCoroot_true]
      congr 2
      ring

theorem weylElement_eq (k : Fin n) (t : Kˣ) :
    weylElement (x n K) k t = torusB K k t * weylB K k := by
  rw [weylElement, x_single, x_neg_single, ← rankOneB_upperSL2, ← rankOneB_lowerSL2,
    ← map_mul, ← map_mul, ← weylSL2_eq, weylSL2_eq_diagSL2_mul, map_mul, torusB_apply, weylB]

theorem weyl (i : Fin n) {β : Fin n → ℤ} (hβ : β ∈ roots (isFiniteType_cartanB n) ∅) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (t : Kˣ) (u : K),
      weylElement (x n K) i t * x n K β u * (weylElement (x n K) i t)⁻¹ =
        x n K (reflection (cartanB n) i β)
          ((ε : K) * ((t ^ (-(∑ j, cartanB n i j * β j)) : Kˣ) : K) * u) := by
  obtain ⟨ε, hε, hn⟩ := weylB_conj_x (K := K) i hβ
  refine ⟨ε, hε, fun t u => ?_⟩
  have hrefl : reflection (cartanB n) i β ∈ roots (isFiniteType_cartanB n) ∅ :=
    (Φ n K).refl_mem i β hβ
  have hii : cartanB n i i = 2 := by simp [cartanB]
  rw [weylElement_eq, _root_.mul_inv_rev,
    show ∀ a b c : spinGroup (quadOdd n K), a * b * c * (b⁻¹ * a⁻¹) = a * (b * c * b⁻¹) * a⁻¹ by
      intros; group,
    hn u, torusB_conj_x i t hrefl, coroot_reflection hii, ← coroot_apply]
  congr 1
  ring

end CFSG.LieType.Steinberg.SpinOdd
