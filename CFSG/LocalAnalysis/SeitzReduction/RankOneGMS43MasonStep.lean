module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43MasonCases

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace GMS43

variable {P : Type*} [Group P]

theorem cases_of_dvd_mul_self_sub_one {m : ℕ} (hm : 1 ≤ m) {b : ℤ}
    (h : (2 : ℤ) ^ m ∣ b * b - 1) :
    (2 : ℤ) ^ m ∣ b + 1 ∨ (2 ≤ m ∧ (2 : ℤ) ^ m ∣ b - 1) ∨
      (3 ≤ m ∧ (2 : ℤ) ^ m ∣ b - (1 + 2 ^ (m - 1))) ∨
        (3 ≤ m ∧ (2 : ℤ) ^ m ∣ b - (-1 + 2 ^ (m - 1))) := by
  have h2m : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ', Nat.sub_add_cancel hm]
  have h2 : (2 : ℤ) ∣ b * b - 1 := (dvd_pow_self 2 (by omega)).trans h
  obtain ⟨c, rfl⟩ : Odd b := by
    rcases Int.even_or_odd b with hb | hb
    · exfalso
      rw [← even_iff_two_dvd, Int.even_sub_one] at h2
      exact h2 (hb.mul_right b)
    · exact hb
  have key : ∃ k : ℤ, 2 * c + 1 = 1 + 2 ^ (m - 1) * k ∨ 2 * c + 1 = -1 + 2 ^ (m - 1) * k := by
    obtain ⟨d, rfl | rfl⟩ := Int.even_or_odd' c
    · have h1 : (2 : ℤ) ^ m ∣ 8 * d * (2 * d + 1) := by
        rw [show 8 * d * (2 * d + 1) = (2 * (2 * d) + 1) * (2 * (2 * d) + 1) - 1 by ring]
        exact h
      have hcop : IsCoprime ((2 : ℤ) ^ m) (2 * d + 1) :=
        IsCoprime.pow_left ⟨-d, 1, by ring⟩
      have h3 := hcop.dvd_of_dvd_mul_right h1
      rw [h2m, show 8 * d = 2 * (4 * d) by ring] at h3
      obtain ⟨k, hk⟩ := Int.dvd_of_mul_dvd_mul_left (by norm_num) h3
      exact ⟨k, Or.inl (by linear_combination hk)⟩
    · have h1 : (2 : ℤ) ^ m ∣ 8 * (d + 1) * (2 * d + 1) := by
        rw [show 8 * (d + 1) * (2 * d + 1) = (2 * (2 * d + 1) + 1) * (2 * (2 * d + 1) + 1) - 1 by
          ring]
        exact h
      have hcop : IsCoprime ((2 : ℤ) ^ m) (2 * d + 1) :=
        IsCoprime.pow_left ⟨-d, 1, by ring⟩
      have h3 := hcop.dvd_of_dvd_mul_right h1
      rw [h2m, show 8 * (d + 1) = 2 * (4 * (d + 1)) by ring] at h3
      obtain ⟨k, hk⟩ := Int.dvd_of_mul_dvd_mul_left (by norm_num) h3
      exact ⟨k, Or.inr (by linear_combination hk)⟩
  obtain ⟨k, hk | hk⟩ := key <;> obtain ⟨l, rfl | rfl⟩ := Int.even_or_odd' k
  ·
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · left
      obtain rfl : m = 1 := by omega
      exact ⟨1 + l, by linear_combination hk⟩
    · exact Or.inr (Or.inl ⟨hm2, ⟨l, by rw [h2m]; linear_combination hk⟩⟩)
  ·
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · interval_cases m
      · exfalso
        norm_num at hk
        omega
      · left
        norm_num at hk ⊢
        exact ⟨1 + l, by linear_combination hk⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hm3, ⟨l, by rw [h2m]; linear_combination hk⟩⟩))
  ·
    left
    exact ⟨l, by rw [h2m]; linear_combination hk⟩
  ·
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · interval_cases m
      · exfalso
        norm_num at hk
        omega
      · right; left
        norm_num at hk ⊢
        exact ⟨l, by linear_combination hk⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hm3, ⟨l, by rw [h2m]; linear_combination hk⟩⟩))

theorem conj_conj_eq_zpow {k y w : P} {b : ℤ} (hk : ∃ a : ℤ, k⁻¹ * w * k = w ^ a)
    (hy : y * w * y⁻¹ = w ^ b) : k * y * k⁻¹ * w * (k * y * k⁻¹)⁻¹ = w ^ b := by
  obtain ⟨a, ha⟩ := hk
  calc k * y * k⁻¹ * w * (k * y * k⁻¹)⁻¹ = k * (y * (k⁻¹ * w * k) * y⁻¹) * k⁻¹ := by group
    _ = k * (y * w * y⁻¹) ^ a * k⁻¹ := by rw [ha, ← conj_zpow]
    _ = k * (w ^ a) ^ b * k⁻¹ := by rw [hy, ← zpow_mul, ← zpow_mul, mul_comm b a]
    _ = (k * w ^ a * k⁻¹) ^ b := by rw [conj_zpow]
    _ = w ^ b := by rw [← ha]; group

theorem zpow_eq_zpow_of_dvd {w : P} {m : ℕ} (hw : orderOf w = 2 ^ m) {b c : ℤ}
    (h : (2 : ℤ) ^ m ∣ b - c) : w ^ b = w ^ c := by
  have h1 : w ^ (b - c) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hw]
    exact_mod_cast h
  calc w ^ b = w ^ (b - c) * w ^ c := by rw [← zpow_add, sub_add_cancel]
    _ = w ^ c := by rw [h1, one_mul]

theorem orderOf_mul_conj_eq {j z w g x : P} {M : Subgroup P} {m : ℕ}
    (hj : j * j = 1)
    (hC : ∀ a b : P, a * j = j * a → b * j = j * b → a * b = b * a)
    (hinv : ∀ y : P, y * j = j * y → y * y = 1 → y = 1 ∨ y = j ∨ y = z ∨ y = j * z)
    (hMn : M.Normal) (hjM : j ∈ M) (hg2 : g * g ∈ M)
    (hMD : ∀ y : P, (∃ h ∈ M, h * j * h⁻¹ = y) ↔ ∃ i : ℤ, y = j * w ^ i)
    (hw : orderOf w = 2 ^ m) (hnot : ∀ i : ℤ, g * j * g⁻¹ ≠ j * w ^ i)
    (huniq : ∀ y : P, IsConj j y → y * j = j * y → y = j ∨ y = x)
    (hcen : ∀ s : P, s * (j * x) = j * x * s) :
    orderOf (j * (g * j * g⁻¹)) = 2 ^ (m + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  set j₁ := g * j * g⁻¹ with hj₁def
  have hj₁M : j₁ ∈ M := hMn.conj_mem j hjM g
  have hj₁ : j₁ * j₁ = 1 := by
    rw [hj₁def, show g * j * g⁻¹ * (g * j * g⁻¹) = g * (j * j) * g⁻¹ by group, hj]
    group
  have hj₁inv : j₁⁻¹ = j₁ := inv_eq_of_mul_eq_one_right hj₁
  have hj₁c : IsConj j j₁ := isConj_iff.mpr ⟨g, rfl⟩
  have hMc : ∀ i : ℤ, IsConj j (j * w ^ i) := fun i => by
    obtain ⟨h, -, hh⟩ := (hMD _).mpr ⟨i, rfl⟩
    exact isConj_iff.mpr ⟨h, hh⟩
  have hjw : j * w * j⁻¹ = w⁻¹ := by
    obtain ⟨h, -, hh⟩ := (hMD (j * w)).mpr ⟨1, by rw [zpow_one]⟩
    have h1 : j * w * (j * w) = 1 := by
      rw [← hh, show h * j * h⁻¹ * (h * j * h⁻¹) = h * (j * j) * h⁻¹ by group, hj]
      group
    rw [hjinv]
    calc j * w * j = j * w * (j * w) * w⁻¹ := by group
      _ = w⁻¹ := by rw [h1, one_mul]
  have hnorm : ∀ h ∈ M, ∃ k : ℤ, h * w * h⁻¹ = w ^ k := by
    intro h hh
    obtain ⟨a, ha⟩ := (hMD (h * j * h⁻¹)).mp ⟨h, hh, rfl⟩
    obtain ⟨h', hh', hh'j⟩ := (hMD (j * w)).mpr ⟨1, by rw [zpow_one]⟩
    obtain ⟨c, hc⟩ := (hMD (h * (j * w) * h⁻¹)).mp
      ⟨h * h', mul_mem hh hh', by rw [← hh'j]; group⟩
    refine ⟨-a + c, ?_⟩
    calc h * w * h⁻¹ = (h * j * h⁻¹)⁻¹ * (h * (j * w) * h⁻¹) := by group
      _ = (j * w ^ a)⁻¹ * (j * w ^ c) := by rw [ha, hc]
      _ = w ^ (-a + c) := by group
  obtain ⟨s, hs⟩ : ∃ s : ℤ, j * j₁ * (j * j₁) = w ^ s := by
    obtain ⟨s, hs⟩ := (hMD (j₁ * j * j₁⁻¹)).mp ⟨j₁, hj₁M, rfl⟩
    refine ⟨s, ?_⟩
    calc j * j₁ * (j * j₁) = j * (j₁ * j * j₁⁻¹) := by rw [hj₁inv]; group
      _ = w ^ s := by rw [hs, ← mul_assoc, hj, one_mul]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  ·
    have hw1 : w = 1 := by rw [← orderOf_eq_one_iff, hw, pow_zero]
    rw [zero_add, pow_one]
    apply orderOf_eq_prime
    · rw [pow_two, hs, hw1, one_zpow]
    · intro h3
      apply hnot 0
      rw [zpow_zero, mul_one]
      calc j₁ = j⁻¹ * (j * j₁) := by group
        _ = j := by rw [h3, mul_one, hjinv]
  have hm1 : 1 ≤ m := hm
  set ρ := w ^ (2 ^ (m - 1)) with hρdef
  obtain ⟨hρ2, hρ1⟩ := rho_mul_self_and_ne_one hm1 hw hρdef.symm
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hρz : w ^ ((2 : ℤ) ^ (m - 1)) = ρ := by
    rw [hρdef, ← zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  have hjρ : j * ρ * j⁻¹ = ρ := by
    rw [hρdef, ← conj_pow, hjw, inv_pow, ← hρdef, hρinv]
  have hρj : ρ * j = j * ρ := by
    calc ρ * j = j * ρ * j⁻¹ * j := by rw [hjρ]
      _ = j * ρ := by group
  have hρx : ρ = j * x := by
    have hc : IsConj j (j * ρ) := by rw [← hρz]; exact hMc _
    rcases huniq _ hc (by rw [mul_assoc, hρj]) with h | h
    · exfalso
      apply hρ1
      calc ρ = j⁻¹ * (j * ρ) := by group
        _ = 1 := by rw [h, inv_mul_cancel]
    · rw [← h, ← mul_assoc, hj, one_mul]
  have hρc : ∀ y : P, y * ρ = ρ * y := fun y => by rw [hρx]; exact hcen y
  have hinv' : ∀ v : P, v * j = j * v → v * v = 1 → v = 1 ∨ v = j ∨ v = ρ ∨ v = j * ρ := by
    have hρne : ρ ≠ j := fun h => hnot 0 (by
      rw [zpow_zero, mul_one, hj₁def, ← h, hρc g, mul_assoc, mul_inv_cancel, mul_one])
    have hzρ : z = ρ ∨ z = j * ρ := by
      rcases hinv ρ hρj hρ2 with h | h | h | h
      · exact absurd h hρ1
      · exact absurd h hρne
      · exact Or.inl h.symm
      · right
        rw [h, ← mul_assoc, hj, one_mul]
    intro v hvj hvv
    rcases hinv v hvj hvv with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hzρ with h' | h' <;> rw [h, h'] <;> simp
    · rcases hzρ with h' | h' <;> rw [h, h']
      · simp
      · rw [← mul_assoc, hj, one_mul]
        simp
  have hnc : j * j₁ ≠ j₁ * j := by
    intro h
    rcases huniq j₁ hj₁c h.symm with h' | h'
    · exact hnot 0 (by rw [zpow_zero, mul_one]; exact h')
    · exact hnot (2 ^ (m - 1)) (by rw [hρz, hρx, ← mul_assoc, hj, one_mul]; exact h')
  set w' := g * w * g⁻¹ with hw'def
  have hw' : orderOf w' = 2 ^ m := by
    rw [hw'def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hw]
  have hw'z : ∀ k : ℤ, w' ^ k = g * w ^ k * g⁻¹ := fun k => by rw [hw'def, conj_zpow]
  have hρ' : w' ^ (2 ^ (m - 1)) = ρ := by
    rw [hw'def, conj_pow, ← hρdef, hρc g, mul_assoc, mul_inv_cancel, mul_one]
  have hρ'z : w' ^ ((2 : ℤ) ^ (m - 1)) = ρ := by
    rw [← zpow_natCast, Nat.cast_pow, Nat.cast_ofNat] at hρ'
    exact hρ'
  obtain ⟨b, hb⟩ := hnorm j₁ hj₁M
  have hww' : w * w' = w' * w := by
    obtain ⟨h', hh', hh'j⟩ := (hMD (j * w)).mpr ⟨1, by rw [zpow_one]⟩
    have hkM : g * h' * g⁻¹ ∈ M := hMn.conj_mem h' hh' g
    obtain ⟨a, ha⟩ := hnorm _ (inv_mem hkM)
    rw [inv_inv] at ha
    have h1 := conj_conj_eq_zpow ⟨a, ha⟩ hb
    have h2 : g * h' * g⁻¹ * j₁ * (g * h' * g⁻¹)⁻¹ = j₁ * w' := by
      rw [hj₁def, hw'def]
      calc g * h' * g⁻¹ * (g * j * g⁻¹) * (g * h' * g⁻¹)⁻¹ = g * (h' * j * h'⁻¹) * g⁻¹ := by
            group
        _ = g * j * g⁻¹ * (g * w * g⁻¹) := by rw [hh'j]; group
    rw [h2] at h1
    have h3 : w' * w * w'⁻¹ = w := by
      calc w' * w * w'⁻¹ = j₁⁻¹ * (j₁ * w' * w * (j₁ * w')⁻¹) * j₁ := by group
        _ = j₁⁻¹ * (j₁ * w * j₁⁻¹) * j₁ := by rw [h1, hb]
        _ = w := by group
    calc w * w' = w' * w * w'⁻¹ * w' := by rw [h3]
      _ = w' * w := by group
  have hjw' : j * w' * j⁻¹ = w' ^ b := by
    obtain ⟨a, ha⟩ := hnorm (g * g) hg2
    have h1 := conj_conj_eq_zpow (k := (g * g)⁻¹) ⟨a, by rw [inv_inv]; exact ha⟩ hb
    have h2 : (g * g)⁻¹ * j₁ * ((g * g)⁻¹)⁻¹ = g⁻¹ * j * g := by rw [hj₁def]; group
    rw [h2] at h1
    rw [hw'z b, hw'def]
    calc j * (g * w * g⁻¹) * j⁻¹ = g * (g⁻¹ * j * g * w * (g⁻¹ * j * g)⁻¹) * g⁻¹ := by group
      _ = g * w ^ b * g⁻¹ := by rw [h1]
  have hj₁w' : j₁ * w' * j₁⁻¹ = w'⁻¹ := by
    rw [hj₁def, hw'def, show g * j * g⁻¹ * (g * w * g⁻¹) * (g * j * g⁻¹)⁻¹ =
      g * (j * w * j⁻¹) * g⁻¹ by group, hjw]
    group
  have hb2 : (2 : ℤ) ^ m ∣ b * b - 1 := by
    have h1 : w ^ (b * b) = w := by
      calc w ^ (b * b) = (w ^ b) ^ b := by rw [zpow_mul]
        _ = (j₁ * w * j₁⁻¹) ^ b := by rw [hb]
        _ = j₁ * (j₁ * w * j₁⁻¹) * j₁⁻¹ := by rw [conj_zpow, ← hb]
        _ = (j₁ * j₁) * w * (j₁ * j₁)⁻¹ := by group
        _ = w := by rw [hj₁]; group
    have h2 : w ^ (b * b - 1) = 1 := by rw [zpow_sub, h1, zpow_one, mul_inv_cancel]
    rw [← orderOf_dvd_iff_zpow_eq_one, hw] at h2
    exact_mod_cast h2
  have hwb : ∀ c : ℤ, (2 : ℤ) ^ m ∣ b - c → w ^ b = w ^ c ∧ w' ^ b = w' ^ c := fun c hc =>
    ⟨zpow_eq_zpow_of_dvd hw hc, zpow_eq_zpow_of_dvd hw' hc⟩
  rcases cases_of_dvd_mul_self_sub_one hm1 hb2 with h | ⟨hm2, h⟩ | ⟨hm3, h⟩ | ⟨hm3, h⟩
  ·
    have he : j₁ * w * j₁⁻¹ = w⁻¹ := by
      rw [hb, (hwb (-1) (by rw [sub_neg_eq_add]; exact h)).1, zpow_neg_one]
    exact orderOf_mul_eq_of_conj_eq_inv hm1 hj hj₁ hw hρdef.symm hjw he hs hinv' hnc hnot
  ·
    exfalso
    obtain ⟨h1, h2⟩ := hwb 1 h
    rw [zpow_one] at h1 h2
    exact false_of_conj_eq_self hm2 hj hj₁ hw hw' hρdef.symm hρ' hρc hww' hjw hj₁w'
      (hb.trans h1) (hjw'.trans h2) hs hC hinv' hnc
  ·
    exfalso
    obtain ⟨h1, h2⟩ := hwb _ h
    rw [zpow_add, zpow_one, hρz] at h1
    rw [zpow_add, zpow_one, hρ'z] at h2
    exact false_of_conj_eq_mul hm3 hj hj₁ hw hw' hρdef.symm hρ' hρc hww' hjw hj₁w'
      (hb.trans h1) (hjw'.trans h2) hs hC hinv' hnc
  ·
    exfalso
    obtain ⟨h1, h2⟩ := hwb _ h
    rw [zpow_add, zpow_neg_one, hρz] at h1
    rw [zpow_add, zpow_neg_one, hρ'z] at h2
    exact false_of_conj_eq_inv_mul hm3 hj hj₁ hw hρdef.symm hρ' hρc hww' hjw
      (hb.trans h1) (hjw'.trans h2) hs hC hinv'

end GMS43

end CFSG.SeitzReduction.RankOne
