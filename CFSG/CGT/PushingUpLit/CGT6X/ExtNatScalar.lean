module

public import CFSG.CGT.PushingUpLit.CGT6X.ExtNatField

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoEight

variable (n : ℕ) [NeZero n]

theorem scalar_S (S : Fq (2 * n) → Fq (2 * n)) (hS : ∀ x y, S (x + y) = S x + S y)
    (hSt : ∀ t : Fq (2 * n), t ≠ 0 → ∀ x, S (t * t * x) = (t * sigR n t)⁻¹ * S x) :
    ∀ x, S x = 0 := by
  have h2 := two_eq_zero_Fq n
  have hS0 : S 0 = 0 := by
    have := hS 0 0
    rw [add_zero] at this
    linear_combination (-1 : Fq (2 * n)) * this
  obtain ⟨a, ha1, ha⟩ := exists_norm_one_ne_one n
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h1a : 1 + a ≠ 0 := by
    intro h
    exact ha1 (by linear_combination h - h2)
  have hc : S 1 = 0 := by
    have e1 := hSt (1 + a) h1a 1
    have e2 : (1 + a) * (1 + a) * 1 = 1 + a * a := by linear_combination a * h2
    rw [e2, hS 1 (a * a)] at e1
    have e3 := hSt a ha0 1
    rw [mul_one, ha, inv_one, one_mul] at e3
    rw [e3] at e1
    have e4 : ((1 + a) * sigR n (1 + a))⁻¹ * S 1 = 0 := by
      rw [← e1]
      linear_combination S 1 * h2
    have hne : ((1 + a) * sigR n (1 + a))⁻¹ ≠ 0 := by
      apply inv_ne_zero
      apply mul_ne_zero h1a
      intro h
      apply h1a
      exact (sigR n).injective (h.trans (map_zero _).symm)
    exact (mul_eq_zero.1 e4).resolve_left hne
  intro x
  obtain ⟨t, rfl⟩ := exists_mul_self_eq n x
  by_cases ht : t = 0
  · rw [ht, mul_zero]
    exact hS0
  · have := hSt t ht 1
    rw [mul_one, hc, mul_zero] at this
    exact this

omit [NeZero n] in
theorem additive_eq_zero {f : Fq (2 * n) → Fq (2 * n)} (hf : ∀ x y, f (x + y) = f x + f y)
    (w : Fq (2 * n) → Fq (2 * n))
    (hw : ∀ t : Fq (2 * n), t ≠ 0 → ∀ x, f (t * t * x) = w t * f x) (a : Fq (2 * n))
    (ha0 : a ≠ 0) (h1a : 1 + a ≠ 0) (hne : w (1 + a) ≠ 1 + w a) : ∀ x, f x = 0 := by
  have h2 := two_eq_zero_Fq n
  have hf0 : f 0 = 0 := by
    have := hf 0 0
    rw [add_zero] at this
    linear_combination (-1 : Fq (2 * n)) * this
  have hc : f 1 = 0 := by
    have e1 := hw (1 + a) h1a 1
    have e2 : (1 + a) * (1 + a) * 1 = 1 + a * a := by linear_combination a * h2
    rw [e2, hf 1 (a * a)] at e1
    have e3 := hw a ha0 1
    rw [mul_one] at e3
    rw [e3] at e1
    have : (w (1 + a) - (1 + w a)) * f 1 = 0 := by linear_combination -e1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  intro x
  obtain ⟨t, rfl⟩ := exists_mul_self_eq n x
  by_cases ht : t = 0
  · rw [ht, mul_zero]
    exact hf0
  · have := hw t ht 1
    rw [mul_one, hc, mul_zero] at this
    exact this

theorem scalar_Y (hn : 2 ≤ n) (Y : Fq (2 * n) → Fq (2 * n)) (hY : ∀ x y, Y (x + y) = Y x + Y y)
    (hYt : ∀ t : Fq (2 * n), t ≠ 0 → ∀ x, Y (t * t * x) = t * (sigR n t)⁻¹ * Y x) :
    ∀ x, Y x = 0 := by
  have h2 := two_eq_zero_Fq n
  obtain ⟨a, ha⟩ := exists_ne_sigR_sq n hn
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply ha
    simp
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply ha
    simp
  have h1a : 1 + a ≠ 0 := by
    intro h
    exact ha1 (by linear_combination h - h2)
  have hb0 : sigR n a ≠ 0 := by
    intro h
    exact ha0 ((sigR n).injective (h.trans (map_zero _).symm))
  have hb1 : 1 + sigR n a ≠ 0 := by
    intro h
    apply ha1
    have h' : sigR n a = 1 := by linear_combination h - h2
    have := congrArg (sigR n) h'
    rwa [sigR_sigR, map_one] at this
  refine additive_eq_zero n hY (fun t => t * (sigR n t)⁻¹) hYt a ha0 h1a ?_
  intro h
  apply ha
  rw [map_add, map_one] at h
  field_simp at h
  linear_combination (-1 : Fq (2 * n)) * h - sigR n a ^ 2 * h2

theorem scalar_P (P : Fq (2 * n) → Fq (2 * n)) (hP : ∀ x y, P (x + y) = P x + P y)
    (hPt : ∀ t : Fq (2 * n), t ≠ 0 → ∀ x, P (t * t * x) = t * sigR n t * P x) :
    ∀ x, P x = 0 := by
  have h2 := two_eq_zero_Fq n
  obtain ⟨a, ha⟩ := exists_add_sigR_ne n
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply ha
    simp
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply ha
    rw [map_one]
    linear_combination h2
  have h1a : 1 + a ≠ 0 := by
    intro h
    exact ha1 (by linear_combination h - h2)
  refine additive_eq_zero n hP (fun t => t * sigR n t) hPt a ha0 h1a ?_
  intro h
  apply ha
  rw [map_add, map_one] at h
  linear_combination h

theorem scalar_one (hn : n = 1) (P Y S : Fq (2 * n) → Fq (2 * n))
    (hS : ∀ x y, S (x + y) = S x + S y)
    (hY : ∀ x y, Y (x + y) = Y x + Y y + S y * x)
    (hP : ∀ x y, P (x + y) = P x + P y + (x * sigR n (Y y) + sigR n x * Y y) +
      x * sigR n x * S y)
    (hSt : ∀ t : Fq (2 * n), t ≠ 0 → ∀ x, S (t * t * x) = (t * sigR n t)⁻¹ * S x)
    (hYt : ∀ t : Fq (2 * n), t ≠ 0 → ∀ x, Y (t * t * x) = t * (sigR n t)⁻¹ * Y x)
    (hPt : ∀ t : Fq (2 * n), t ≠ 0 → ∀ x, P (t * t * x) = t * sigR n t * P x) :
    ∃ d : Fq (2 * n), sigR n d = d ∧ (∀ x, S x = 0) ∧ (∀ x, Y x = d * x) ∧
      ∀ x, P x = d * (x * sigR n x) := by
  have h2 := two_eq_zero_Fq n
  have hS0 := scalar_S n S hS hSt
  have hcube : ∀ t : Fq (2 * n), t ≠ 0 → t ^ 3 = 1 := by
    intro t ht
    have : Fintype (Fq (2 * n)) := Fintype.ofFinite _
    have hc : Fintype.card (Fq (2 * n)) = 4 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * n) (by have := NeZero.ne n; omega)]
      have : 2 ^ (2 * n) = 4 := by rw [hn]; norm_num
      exact this
    have := FiniteField.pow_card_sub_one_eq_one t ht
    rwa [hc] at this
  have hsig : ∀ x : Fq (2 * n), sigR n x = x * x := fun x => by
    rw [sigR_apply]
    have : 2 ^ n = 2 := by rw [hn]; norm_num
    rw [this]
    ring
  have hY0 : Y 0 = 0 := by
    have := hY 0 0
    rw [add_zero, hS0, zero_mul, add_zero] at this
    linear_combination (-1 : Fq (2 * n)) * this
  have hP0 : P 0 = 0 := by
    have := hP 0 0
    rw [add_zero, hS0, hY0, map_zero] at this
    linear_combination (-1 : Fq (2 * n)) * this
  set d : Fq (2 * n) := Y 1 with hd
  have hYx : ∀ x, Y x = d * x := by
    intro x
    obtain ⟨t, rfl⟩ := exists_mul_self_eq n x
    by_cases ht : t = 0
    · rw [ht, mul_zero, hY0, mul_zero]
    · have h := hYt t ht 1
      rw [mul_one] at h
      rw [h, hsig]
      have h3 := hcube t ht
      have : t * (t * t)⁻¹ = t * t := by
        field_simp
        linear_combination (-1 : Fq (2 * n)) * h3
      rw [this, hd]
      ring
  set e : Fq (2 * n) := P 1 with he
  have hPx : ∀ x, x ≠ 0 → P x = e := by
    intro x hx
    obtain ⟨t, rfl⟩ := exists_mul_self_eq n x
    have ht : t ≠ 0 := by
      rintro rfl
      exact hx (mul_zero 0)
    have h := hPt t ht 1
    rw [mul_one] at h
    rw [h, hsig, he]
    have h3 := hcube t ht
    have : t * (t * t) = 1 := by linear_combination h3
    rw [this, one_mul]
  have hnorm : ∀ x : Fq (2 * n), x ≠ 0 → x * sigR n x = 1 := by
    intro x hx
    rw [hsig]
    have := hcube x hx
    linear_combination this
  have hdσ : sigR n d = d := by
    have h11 := hP 1 1
    have h1 : (1 : Fq (2 * n)) + 1 = 0 := by linear_combination h2
    rw [h1, hP0, hS0, hYx 1, mul_one, map_one, mul_zero, add_zero, one_mul, ← he] at h11
    linear_combination (-1 : Fq (2 * n)) * h11 - (e + d) * h2
  obtain ⟨w, hw⟩ := exists_sigR_ne n
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (map_zero _)
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hw (map_one _)
  have h1w : 1 + w ≠ 0 := by
    intro h
    exact hw1 (by linear_combination h - h2)
  have hww : w * w + w + 1 = 0 := by
    have h3 := hcube w hw0
    have : (w - 1) * (w * w + w + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hw1)
  have hed : e = d := by
    have h := hP 1 w
    rw [hPx _ h1w, hS0, hYx w, map_mul, hdσ, hPx w hw0, ← he, hsig w] at h
    simp only [map_one, mul_zero, add_zero, one_mul] at h
    linear_combination (-1 : Fq (2 * n)) * h - d * hww
  refine ⟨d, hdσ, hS0, hYx, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, hP0, zero_mul, mul_zero]
  · rw [hPx x hx, hnorm x hx, mul_one, hed]

end CFSG.CGT.PushingUpLit.CGT6X
