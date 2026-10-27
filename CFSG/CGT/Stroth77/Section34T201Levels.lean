module

public import CFSG.CGT.Stroth77.Section34T201Mats

public section

namespace CFSG.CGT.Stroth77

namespace Stroth34T201Levels

open Matrix

theorem not_two_pow_dvd_sq_entry {q : ℕ} {a₂₀ a₀₁ a₂₁ a₁₁ a₂₂ s₁ s₂ : ℤ}
    (h₂₀ : (2 : ℤ) ^ (q + 3) ∣ a₂₀) (h₀₁ : (2 : ℤ) ^ (q + 1) ∣ a₀₁)
    (h₂₁ : (2 : ℤ) ^ (q + 3) ∣ a₂₁ - 2 ^ (q + 2)) (h₁₁ : (2 : ℤ) ^ (q + 3) ∣ a₁₁ - 1 - s₁)
    (h₂₂ : (2 : ℤ) ^ (q + 3) ∣ a₂₂ - 1 - s₂) (hs₁ : (4 : ℤ) ∣ s₁) (hs₂ : (4 : ℤ) ∣ s₂) :
    ¬ (2 : ℤ) ^ (q + 4) ∣ a₂₀ * a₀₁ + a₂₁ * a₁₁ + a₂₂ * a₂₁ := by
  rintro ⟨w, hw⟩
  obtain ⟨x, hx⟩ := h₂₀
  obtain ⟨y, hy⟩ := h₀₁
  obtain ⟨z, hz⟩ := h₂₁
  obtain ⟨u₁, hu₁⟩ := h₁₁
  obtain ⟨u₂, hu₂⟩ := h₂₂
  obtain ⟨v₁, hv₁⟩ := hs₁
  obtain ⟨v₂, hv₂⟩ := hs₂
  have key : (2 : ℤ) ^ (q + 3) * (2 * (w - 2 ^ q * x * y - z
      - (v₁ + v₂ + 2 ^ (q + 1) * (u₁ + u₂)) - 2 * z * (v₁ + v₂ + 2 ^ (q + 1) * (u₁ + u₂)))) =
      (2 : ℤ) ^ (q + 3) * 1 := by
    have e₂₀ : a₂₀ = 2 ^ (q + 3) * x := hx
    have e₀₁ : a₀₁ = 2 ^ (q + 1) * y := hy
    have e₂₁ : a₂₁ = 2 ^ (q + 2) + 2 ^ (q + 3) * z := by linear_combination hz
    have e₁₁ : a₁₁ = 1 + 4 * v₁ + 2 ^ (q + 3) * u₁ := by linear_combination hu₁ + hv₁
    have e₂₂ : a₂₂ = 1 + 4 * v₂ + 2 ^ (q + 3) * u₂ := by linear_combination hu₂ + hv₂
    rw [e₂₀, e₀₁, e₂₁, e₁₁, e₂₂] at hw
    linear_combination (-1 : ℤ) * hw
  have h1 := mul_left_cancel₀ (pow_ne_zero (q + 3) (two_ne_zero : (2 : ℤ) ≠ 0)) key
  generalize w - 2 ^ q * x * y - z - (v₁ + v₂ + 2 ^ (q + 1) * (u₁ + u₂)) -
    2 * z * (v₁ + v₂ + 2 ^ (q + 1) * (u₁ + u₂)) = E at h1
  omega

theorem wMat_apply (q : ℕ) (i : Fin 3) (r c : Fin 3) :
    wMat (q + 1) i r c = ![![![1, 0, 0], ![0, 1, 2 ^ (q + 2)], ![0, 2 ^ (q + 2), 1]],
      ![![1, 0, 0], ![0, 1 + 2 ^ (q + 2), 2 ^ (q + 2)], ![0, 0, 1 + 2 ^ (q + 2)]],
      ![![1, 0, 0], ![0, 1 + 2 ^ (q + 2), 0], ![0, 2 ^ (q + 2), 1 + 2 ^ (q + 2)]]] i c r := by
  fin_cases i <;> simp [wMat, ofCols_apply]

theorem not_matEq_sq_of_wMat {p : ℕ} (hp : 2 ≤ p) (i : Fin 3) {M T : IntMat}
    (hM : MatEq (Type200.k (p - 1)) M (wMat (p - 1) i)) (hT₁ : T 1 2 = 0) (hT₂ : T 2 1 = 0) :
    ¬ MatEq (Type200.k p) (M * M) T := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  rw [show q + 2 - 1 = q + 1 by omega] at hM
  intro hsq
  have hk : ∀ r c, (2 : ℤ) ^ (Type200.k (q + 1) r) ∣ wMat (q + 1) i r c - M r c :=
    fun r c => Int.modEq_iff_dvd.mp (hM r c)
  have e₂₀ := hk 2 0
  have e₁₀ := hk 1 0
  have e₀₁ := hk 0 1
  have e₀₂ := hk 0 2
  have e₁₁ := hk 1 1
  have e₂₂ := hk 2 2
  have e₂₁ := hk 2 1
  have e₁₂ := hk 1 2
  simp only [Type200.k, wMat_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at e₂₀ e₁₀ e₀₁ e₀₂ e₁₁ e₂₂ e₂₁ e₁₂
  have h4 : (4 : ℤ) ∣ 2 ^ (q + 2) := ⟨2 ^ q, by ring⟩
  have neg : ∀ {n : ℕ} {a : ℤ}, (2 : ℤ) ^ n ∣ 0 - a → (2 : ℤ) ^ n ∣ a := fun h => by
    simpa using h
  have flip : ∀ {n : ℕ} {a b : ℤ}, (2 : ℤ) ^ n ∣ b - a → (2 : ℤ) ^ n ∣ a - b := fun h => by
    rw [← neg_sub]; exact h.neg_right
  have h21 := Int.modEq_iff_dvd.mp (hsq 2 1)
  have h12 := Int.modEq_iff_dvd.mp (hsq 1 2)
  simp only [Type200.k, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.head_cons, hT₁, hT₂, Matrix.mul_apply, Fin.sum_univ_three] at h21 h12
  fin_cases i
  ·
    refine not_two_pow_dvd_sq_entry (s₁ := 0) (s₂ := 0) (neg e₂₀) (neg e₀₁)
      (flip e₂₁) (by simpa using flip e₁₁) (by simpa using flip e₂₂) (dvd_zero _) (dvd_zero _) ?_
    have := h21.neg_right
    rw [neg_sub, sub_zero] at this
    exact this
  ·
    refine not_two_pow_dvd_sq_entry (s₁ := 2 ^ (q + 2)) (s₂ := 2 ^ (q + 2)) (neg e₂₀) (neg e₀₁)
      (flip e₂₁) (by simpa [sub_sub] using flip e₁₁) (by simpa [sub_sub] using flip e₂₂) h4 h4 ?_
    have := h21.neg_right
    rw [neg_sub, sub_zero] at this
    exact this
  ·
    refine not_two_pow_dvd_sq_entry (s₁ := 2 ^ (q + 2)) (s₂ := 2 ^ (q + 2)) (neg e₁₀) (neg e₀₂)
      (flip e₁₂) (by simpa [sub_sub] using flip e₁₁) (by simpa [sub_sub] using flip e₂₂) h4 h4 ?_
    have := h12.neg_right
    rw [neg_sub, sub_zero] at this
    convert this using 1; ring

theorem not_matEq_sq_one_of_wMat {p : ℕ} (hp : 2 ≤ p) (i : Fin 3) {M : IntMat}
    (hM : MatEq (Type200.k (p - 1)) M (wMat (p - 1) i)) :
    ¬ MatEq (Type200.k p) (M * M) 1 :=
  not_matEq_sq_of_wMat hp i hM (by simp) (by simp)

theorem not_matEq_sq_eMat_of_wMat {m : ℕ} (hm : 2 ≤ m) (i : Fin 3) {M : IntMat}
    (hM : MatEq (Type200.k (m - 1)) M (wMat (m - 1) i)) :
    ¬ MatEq (Type201.k m) (M * M) 1 ∧ ¬ MatEq (Type201.k m) (M * M) (eMat m) :=
  ⟨not_matEq_sq_of_wMat hm i hM (by simp) (by simp),
    not_matEq_sq_of_wMat hm i hM (by simp [eMat, ofCols_apply]) (by simp [eMat, ofCols_apply])⟩

theorem matEq_one_of_levels {m : ℕ} (hm : 2 ≤ m) {M : IntMat}
    (hA : ∀ {M : IntMat}, Compat (Type200.k 1) M → IsAut1 (Type200.k 1) M →
      MatEq (Type200.k 1) (M * Type200.uvM) (Type200.uvM * M) →
      MatEq (Type200.k 1) (M * Type200.tM) (Type200.tM * M) →
      NatCond (Type200.k 1) M → ¬ MatEq (Type200.k 1) M 1 → ∃ i, MatEq (Type200.k 1) M (wMat 1 i))
    (hB : ∀ {p : ℕ}, 2 ≤ p → ∀ {M : IntMat}, Compat (Type200.k p) M →
      MatEq (Type200.k (p - 1)) M 1 →
      MatEq (Type200.k p) (M * Type200.uvM) (Type200.uvM * M) →
      MatEq (Type200.k p) (M * Type200.tM) (Type200.tM * M) →
      NatCond (Type200.k p) M → ¬ MatEq (Type200.k p) M 1 → ∃ i, MatEq (Type200.k p) M (wMat p i))
    (hc : ∀ p, 1 ≤ p → p ≤ m - 1 → Compat (Type200.k p) M)
    (h1 : IsAut1 (Type200.k 1) M)
    (huv : ∀ p, 1 ≤ p → p ≤ m - 1 → MatEq (Type200.k p) (M * Type200.uvM) (Type200.uvM * M))
    (ht : ∀ p, 1 ≤ p → p ≤ m - 1 → MatEq (Type200.k p) (M * Type200.tM) (Type200.tM * M))
    (hnat : ∀ p, 1 ≤ p → p ≤ m - 1 → NatCond (Type200.k p) M)
    (hsq : ∀ p, 1 ≤ p → p ≤ m - 1 → MatEq (Type200.k p) (M * M) 1)
    (hsq₀ : MatEq (Type201.k m) (M * M) 1 ∨ MatEq (Type201.k m) (M * M) (eMat m)) :
    MatEq (Type200.k (m - 1)) M 1 := by
  have lift : ∀ q, 2 ≤ q → q ≤ m → ∀ i, MatEq (Type200.k (q - 1)) M (wMat (q - 1) i) → False := by
    intro q hq hqm i hi
    rcases Nat.lt_or_ge q m with hlt | hge
    · exact not_matEq_sq_one_of_wMat hq i hi (hsq q (by omega) (by omega))
    · obtain rfl : q = m := le_antisymm hqm hge
      have := not_matEq_sq_eMat_of_wMat hm i hi
      rcases hsq₀ with h | h
      exacts [this.1 h, this.2 h]
  have key : ∀ p, 1 ≤ p → p ≤ m - 1 → MatEq (Type200.k p) M 1 := by
    intro p hp1 hpm
    induction p, hp1 using Nat.le_induction with
    | base =>
      by_contra hne
      obtain ⟨i, hi⟩ := hA (hc 1 le_rfl hpm) h1 (huv 1 le_rfl hpm) (ht 1 le_rfl hpm)
        (hnat 1 le_rfl hpm) hne
      exact lift 2 le_rfl hm i hi
    | succ p hp ih =>
      by_contra hne
      have hN : MatEq (Type200.k (p + 1 - 1)) M 1 := by
        rw [Nat.add_sub_cancel]; exact ih (by omega)
      obtain ⟨i, hi⟩ := hB (p := p + 1) (by omega) (hc (p + 1) (by omega) hpm) hN
        (huv (p + 1) (by omega) hpm) (ht (p + 1) (by omega) hpm) (hnat (p + 1) (by omega) hpm) hne
      exact lift (p + 2) (by omega) (by omega) i hi
  exact key (m - 1) (by omega) le_rfl

end Stroth34T201Levels

end CFSG.CGT.Stroth77
