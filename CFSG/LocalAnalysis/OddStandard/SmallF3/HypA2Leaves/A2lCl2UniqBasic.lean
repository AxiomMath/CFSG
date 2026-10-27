module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open

@[expose] def cl24E : StatedLieTag → ℕ → ℕ
  | .PSL, n => n
  | .PSU, n => if Even n then 2 * (n - 1) else 2 * n
  | .PSp, n => 2 * n
  | .POmegaOdd, n => 2 * n
  | .POmegaPlus, n => 2 * (n - 1)
  | .POmegaMinus, n => 2 * n
  | .G2, _ => 6
  | .F4, _ => 12
  | .E6, _ => 12
  | .E7, _ => 18
  | .E8, _ => 30
  | .twistedE6, _ => 18
  | .trialityD4, _ => 12
  | .twistedB2, _ => 4
  | .twistedG2, _ => 6
  | .twistedF4, _ => 12
  | .Tits, _ => 0

@[expose] def Cl24CofMod (C j : ℕ) : Prop :=
  ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (C : ℤ) ≡ s * (3 ^ (2 * j) - 1) [ZMOD 3 ^ (2 * j + 1)]

theorem cl24_dvd_of_ppd_dvd {k j ℓ : ℕ} (hk : 0 < k) (hℓ : ℓ ∣ 3 ^ k - 1)
    (hprim : ∀ i : ℕ, 0 < i → i < k → ¬ ℓ ∣ 3 ^ i - 1) (hj : ℓ ∣ 3 ^ j - 1) : k ∣ j := by
  have hg : ℓ ∣ 3 ^ (Nat.gcd k j) - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd hℓ hj
  by_contra hkj
  have hgk : Nat.gcd k j < k :=
    lt_of_le_of_ne (Nat.gcd_le_left _ hk) (fun h => hkj (h ▸ Nat.gcd_dvd_right k j))
  exact hprim _ (Nat.gcd_pos_of_pos_left _ hk) hgk hg

theorem cl24_exists_ppd {k : ℕ} (hk : 3 ≤ k) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i := by
  obtain ⟨ℓ, hℓ, hℓd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := 3) le_rfl (n := k) hk
  refine ⟨ℓ, hℓ, ?_, ?_, fun j => ⟨cl24_dvd_of_ppd_dvd (by omega) hℓd hprim, fun hkj => ?_⟩⟩
  · rintro rfl
    exact hprim 1 one_pos (by omega) (by norm_num)
  · rintro rfl
    have h1 : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
    have h2 := Nat.dvd_sub h1 hℓd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
  · obtain ⟨c, rfl⟩ := hkj
    rw [pow_mul]
    exact hℓd.trans (by simpa using Nat.sub_dvd_pow_sub_pow (3 ^ k) 1 c)

theorem cl24_dvd_of_dvd_sub {ℓ k j e : ℕ} (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i)
    (h : ℓ ∣ (3 ^ j) ^ e - 1) : k ∣ j * e := by
  rw [← pow_mul] at h
  exact (hk _).1 h

theorem cl24_dvd_of_dvd_add {ℓ k j e : ℕ} (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i)
    (h : ℓ ∣ (3 ^ j) ^ e + 1) : k ∣ 2 * (j * e) := by
  refine (hk _).1 ?_
  have hsq : 3 ^ (2 * (j * e)) - 1 = ((3 ^ j) ^ e + 1) * ((3 ^ j) ^ e - 1) := by
    have h1 : 3 ^ (2 * (j * e)) = ((3 ^ j) ^ e) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [h1]
    simpa using Nat.sq_sub_sq ((3 ^ j) ^ e) 1
  rw [hsq]
  exact dvd_mul_of_dvd_left h _

theorem cl24_dvd_sub_of {ℓ k j e : ℕ} (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i)
    (h : k ∣ j * e) : ℓ ∣ (3 ^ j) ^ e - 1 := by
  rw [← pow_mul]
  exact (hk _).2 h

theorem cl24_dvd_add_of {ℓ k j e : ℕ} (hℓ : ℓ.Prime) (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i)
    (h : k = 2 * (j * e)) (he : 0 < j * e) : ℓ ∣ (3 ^ j) ^ e + 1 := by
  have hdiv : ℓ ∣ 3 ^ (2 * (j * e)) - 1 := (hk _).2 (h ▸ dvd_rfl)
  have hsq : 3 ^ (2 * (j * e)) - 1 = ((3 ^ j) ^ e + 1) * ((3 ^ j) ^ e - 1) := by
    have h1 : 3 ^ (2 * (j * e)) = ((3 ^ j) ^ e) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [h1]
    simpa using Nat.sq_sub_sq ((3 ^ j) ^ e) 1
  rw [hsq] at hdiv
  rcases (Nat.Prime.dvd_mul hℓ).1 hdiv with h1 | h1
  · exact h1
  · exfalso
    rw [← pow_mul] at h1
    have := (hk _).1 h1
    have := Nat.le_of_dvd he this
    omega

theorem cl24_size_of_digit {D D' j : ℕ}
    (hX : ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      s * (D' : ℤ) - s' * (D : ℤ) ≠ 0 ∧ (3 : ℤ) ^ (2 * j) ∣ s * (D' : ℤ) - s' * (D : ℤ)) :
    3 ^ (2 * j) ≤ D + D' := by
  obtain ⟨s, s', hs, hs', hne, hdvd⟩ := hX
  have h1 : (3 ^ (2 * j) : ℕ) ∣ (s * (D' : ℤ) - s' * (D : ℤ)).natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hdvd
    simpa using this
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hne) h1
  refine h2.trans ?_
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> omega

theorem cl24_bernoulli (m : ℕ) : 2 * m + 1 ≤ 3 ^ m := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem cl24_pow_two_mul (j : ℕ) : 3 ^ (2 * j) = 3 ^ j * 3 ^ j := by
  rw [two_mul, pow_add]

theorem cl24_digit_contra4 {D D' j : ℕ} (hj : 1 ≤ j) (hD : D ≤ 3 ^ j + 1) (hD' : D' ≤ 4 * j) :
    D + D' < 3 ^ (2 * j) := by
  have h1 := cl24_bernoulli j
  rw [cl24_pow_two_mul]
  rcases Nat.lt_or_ge j 2 with h | h
  · obtain rfl : j = 1 := by omega
    norm_num at *
    omega
  · have h9 : 9 ≤ 3 ^ j :=
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h
    nlinarith [Nat.mul_le_mul_right (3 ^ j) h9]

theorem cl24_digit_contra6 {D D' j : ℕ} (hj : 2 ≤ j) (hD : D ≤ 3 ^ j + 1) (hD' : D' ≤ 6 * j) :
    D + D' < 3 ^ (2 * j) := by
  have h1 := cl24_bernoulli j
  rw [cl24_pow_two_mul]
  have h9 : 9 ≤ 3 ^ j :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  nlinarith [Nat.mul_le_mul_right (3 ^ j) h9]

theorem cl24_tri (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
  Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self n))

theorem cl24_cross_NE {N N' E E' j d : ℕ} (hj : 0 < j) (hd : 0 < d) (hN : N * j = N' * d)
    (hE : j * E = d * E') : N * E' = N' * E := by
  have h : (j * d) * (N * E') = (j * d) * (N' * E) :=
    calc (j * d) * (N * E') = (N * j) * (d * E') := by ring
      _ = (N' * d) * (j * E) := by rw [hN, hE]
      _ = (j * d) * (N' * E) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hj hd) h

theorem cl24_E_lt {E E' j d : ℕ} (hj : 0 < j) (hjd : j < d) (hE : j * E = d * E')
    (hE' : 0 < E') : E' < E := by
  by_contra h
  push_neg at h
  nlinarith [Nat.mul_le_mul_left j h, Nat.mul_lt_mul_of_pos_right hjd hE']

@[expose] def Cl24PM (j : ℕ) (x : ℤ) : Prop :=
  ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ x ≡ s [ZMOD 3 ^ (2 * j + 1)]

theorem cl24PM_one (j : ℕ) : Cl24PM j 1 :=
  ⟨1, Or.inl rfl, Int.ModEq.refl _⟩

theorem cl24PM_mul {j : ℕ} {x y : ℤ} (hx : Cl24PM j x) (hy : Cl24PM j y) :
    Cl24PM j (x * y) := by
  obtain ⟨s, hs, hxs⟩ := hx
  obtain ⟨t, ht, hyt⟩ := hy
  refine ⟨s * t, ?_, hxs.mul hyt⟩
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp

theorem cl24PM_prod {ι : Type*} {j : ℕ} (s : Finset ι) (f : ι → ℤ)
    (h : ∀ i ∈ s, Cl24PM j (f i)) : Cl24PM j (∏ i ∈ s, f i) :=
  Finset.prod_induction f (Cl24PM j) (fun _ _ => cl24PM_mul) (cl24PM_one j) h

theorem cl24PM_pow_sub {j e : ℕ} (hj : 1 ≤ j) (he : 3 ≤ e) :
    Cl24PM j ((((3 ^ j) ^ e - 1 : ℕ)) : ℤ) := by
  refine ⟨-1, Or.inr rfl, ?_⟩
  have h1 : 1 ≤ (3 ^ j) ^ e := Nat.one_le_pow _ _ (by positivity)
  have hdvd : (3 : ℤ) ^ (2 * j + 1) ∣ (((3 ^ j) ^ e : ℕ) : ℤ) := by
    have : 3 ^ (2 * j + 1) ∣ (3 ^ j) ^ e := by
      rw [← pow_mul]
      exact pow_dvd_pow 3 (by nlinarith)
    exact_mod_cast this
  have h0 : (((3 ^ j) ^ e : ℕ) : ℤ) ≡ 0 [ZMOD 3 ^ (2 * j + 1)] :=
    (Int.modEq_zero_iff_dvd).2 hdvd
  rw [Nat.cast_sub h1]
  simpa using h0.sub_right 1

theorem cl24PM_pow_add {j e : ℕ} (hj : 1 ≤ j) (he : 3 ≤ e) :
    Cl24PM j ((((3 ^ j) ^ e + 1 : ℕ)) : ℤ) := by
  refine ⟨1, Or.inl rfl, ?_⟩
  have hdvd : (3 : ℤ) ^ (2 * j + 1) ∣ (((3 ^ j) ^ e : ℕ) : ℤ) := by
    have : 3 ^ (2 * j + 1) ∣ (3 ^ j) ^ e := by
      rw [← pow_mul]
      exact pow_dvd_pow 3 (by nlinarith)
    exact_mod_cast this
  have h0 : (((3 ^ j) ^ e : ℕ) : ℤ) ≡ 0 [ZMOD 3 ^ (2 * j + 1)] :=
    (Int.modEq_zero_iff_dvd).2 hdvd
  push_cast
  simpa using h0.add_right 1

theorem cl24CofMod_of_mul {j R : ℕ} (hj : 1 ≤ j) (hR : Cl24PM j (R : ℤ)) :
    Cl24CofMod (((3 ^ j) ^ 2 - 1) * R) j := by
  obtain ⟨s, hs, hRs⟩ := hR
  refine ⟨s, hs, ?_⟩
  have h1 : 1 ≤ (3 ^ j) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : ((((3 : ℕ) ^ j) ^ 2 - 1 : ℕ) : ℤ) = 3 ^ (2 * j) - 1 := by
    rw [Nat.cast_sub h1]
    push_cast
    rw [← pow_mul, mul_comm]
  rw [Nat.cast_mul, h2]
  exact (Int.ModEq.mul_left _ hRs).trans (by rw [mul_comm (3 ^ (2 * j) - 1 : ℤ) s])

theorem cl24CofMod_of_prod {ι : Type*} [DecidableEq ι] {j : ℕ} {s : Finset ι} {f : ι → ℕ}
    {i₀ : ι} (hj : 1 ≤ j) (hi : i₀ ∈ s) (h0 : f i₀ = (3 ^ j) ^ 2 - 1)
    (h : ∀ i ∈ s.erase i₀, Cl24PM j ((f i : ℕ) : ℤ)) : Cl24CofMod (∏ i ∈ s, f i) j := by
  rw [← Finset.mul_prod_erase s f hi, h0]
  refine cl24CofMod_of_mul hj ?_
  rw [Nat.cast_prod]
  exact cl24PM_prod _ _ h

end CFSG.OddStandard.SmallF3.HypA2Leaves
