module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25Dihedral
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

open Subgroup

variable {G : Type*} [Group G] {𝒞 : Set G}

theorem bareDatum_extend {e : ℕ} {s t₀ : G} (hs2 : s * s = 1) (ht₀2 : t₀ * t₀ = 1)
    (hord : orderOf (t₀ * s) = 2 ^ (e + 2)) : BareDatum (e + 1) (t₀ * s) t₀ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have ht₀i : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀2
  have hinv : t₀ * (t₀ * s) * t₀ = (t₀ * s)⁻¹ :=
    calc t₀ * (t₀ * s) * t₀ = (t₀ * t₀) * s * t₀ := by group
      _ = s * t₀ := by rw [ht₀2, one_mul]
      _ = s⁻¹ * t₀⁻¹ := by rw [hsi, ht₀i]
      _ = (t₀ * s)⁻¹ := (mul_inv_rev t₀ s).symm
  refine ⟨hord, ht₀2, hinv, ?_⟩
  intro hmem
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hmem
  have hcomm : (t₀ * s) * t₀ = t₀ * (t₀ * s) :=
    calc (t₀ * s) * t₀ = (t₀ * s) * (t₀ * s) ^ i := by rw [hi]
      _ = (t₀ * s) ^ i * (t₀ * s) := (Commute.self_zpow (t₀ * s) i).eq
      _ = t₀ * (t₀ * s) := by rw [hi]
  have hsq : (t₀ * s) * (t₀ * s) = 1 := by
    have h1 : (t₀ * s)⁻¹ = t₀ * s := by
      rw [← hinv, ← hcomm]
      calc (t₀ * s) * t₀ * t₀ = (t₀ * s) * (t₀ * t₀) := by group
        _ = t₀ * s := by rw [ht₀2, mul_one]
    exact mul_eq_one_iff_eq_inv.mpr h1.symm
  have := orderOf_dvd_of_pow_eq_one (show (t₀ * s) ^ 2 = 1 by rw [sq]; exact hsq)
  rw [hord] at this
  have h2 : 2 ^ (e + 2) ≤ 2 := Nat.le_of_dvd (by norm_num) this
  have h3 : 4 ≤ 2 ^ (e + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem conj_s_eq {w' s t₀ : G} (hs : s = w'⁻¹ * t₀) (ht : ∀ i : ℤ, t₀ * w' ^ i = w' ^ (-i) * t₀)
    (j : ℤ) : w' ^ j * s * (w' ^ j)⁻¹ = w' ^ (2 * j - 1) * t₀ := by
  rw [hs]
  calc w' ^ j * (w'⁻¹ * t₀) * (w' ^ j)⁻¹ = w' ^ (j - 1) * (t₀ * w' ^ (-j)) := by group
    _ = w' ^ (j - 1) * (w' ^ (-(-j)) * t₀) := by rw [ht]
    _ = w' ^ (2 * j - 1) * t₀ := by group

theorem datum_extend (hconj : ∀ g u, u ∈ 𝒞 → g * u * g⁻¹ ∈ 𝒞) {e : ℕ} {w t : G}
    (hd : Datum 𝒞 e w t) {s t₀ : G} (hs𝒞 : s ∈ 𝒞) (hs2 : s * s = 1)
    (hsn : ∀ d ∈ dsub w t, s * d * s ∈ dsub w t) (ht₀ : t₀ ∈ dsub w t) (ht₀2 : t₀ * t₀ = 1)
    (hord : orderOf (t₀ * s) = 2 ^ (e + 2)) : Datum 𝒞 (e + 1) (t₀ * s) t₀ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have ht₀i : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀2
  have hb := bareDatum_extend hs2 ht₀2 hord
  have hw2 : (t₀ * s) ^ 2 ∈ dsub w t := by
    have : (t₀ * s) ^ 2 = t₀ * (s * t₀ * s) := by rw [sq]; group
    rw [this]
    exact mul_mem ht₀ (hsn t₀ ht₀)
  have hs_eq : s = (t₀ * s)⁻¹ * t₀ := by
    rw [mul_inv_rev, hsi, ht₀i, mul_assoc, ht₀2, mul_one]
  have hkey := conj_s_eq hs_eq hb.t_zpow
  refine ⟨hb, ?_⟩
  intro g hg hg2 hg1
  rcases hb.eq_center_or_refl hg hg2 hg1 with rfl | ⟨i, rfl⟩
  · have hmemD : (t₀ * s) ^ (2 ^ (e + 1 + 0)) ∈ dsub w t := by
      have : (t₀ * s) ^ (2 ^ (e + 1)) = ((t₀ * s) ^ 2) ^ (2 ^ e) := by
        rw [← pow_mul, ← pow_succ']
      rw [add_zero, this]
      exact pow_mem hw2 _
    exact hd.inv_mem _ (by simpa using hmemD) hg2 hg1
  · obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
    · have : (t₀ * s) ^ (2 * k) * t₀ ∈ dsub w t := by
        rw [zpow_mul]
        exact mul_mem (zpow_mem (by simpa using hw2) k) ht₀
      exact hd.inv_mem _ this hg2 hg1
    · have := hconj ((t₀ * s) ^ (k + 1)) s hs𝒞
      rw [hkey (k + 1)] at this
      convert this using 3
      ring
  
theorem BareDatum.zpow_eq_one_iff {e : ℕ} {w t : G} (hd : BareDatum e w t) {N : ℤ} :
    w ^ N = 1 ↔ (2 : ℤ) ^ (e + 1) ∣ N := by
  rw [← orderOf_dvd_iff_zpow_eq_one, hd.order_w]; push_cast; rfl

theorem BareDatum.zpow_eq_zpow_iff {e : ℕ} {w t : G} (hd : BareDatum e w t) {N M : ℤ} :
    w ^ N = w ^ M ↔ (2 : ℤ) ^ (e + 1) ∣ N - M := by
  rw [← hd.zpow_eq_one_iff, zpow_sub, mul_inv_eq_one]

@[expose] def FixLeTwo (s : G) (D : Subgroup G) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, s * a * s = a → s * b * s = b → s * c * s = c →
    a = b ∨ a = c ∨ b = c

theorem exists_dvd_mul_add {m : ℤ} (hm : Odd m) (n : ℕ) (b : ℤ) :
    ∃ i : ℤ, (2 : ℤ) ^ n ∣ m * i + b := by
  have hc : IsCoprime m ((2 : ℤ) ^ n) := (Int.isCoprime_two_right.mpr hm).pow_right
  obtain ⟨u, v, huv⟩ := hc
  exact ⟨-b * u, b * v, by linear_combination (-b) * huv⟩

theorem conj_involution_cancel {s : G} (hs2 : s * s = 1) (g : G) : s * (s * g * s) * s = g := by
  calc s * (s * g * s) * s = (s * s) * g * (s * s) := by group
    _ = g := by rw [hs2, one_mul, mul_one]

theorem conj_rot_mem {e : ℕ} {w t s : G} (hd : BareDatum e w t) (hs2 : s * s = 1)
    (hsn : ∀ d ∈ dsub w t, s * d * s ∈ dsub w t) (he : 1 ≤ e) : s * w * s ∈ zpowers w := by
  have hmemD : s * w * s ∈ dsub w t := hsn w (mem_sup_left (mem_zpowers w))
  obtain ⟨i, h | h⟩ := (hd.mem_dsub_iff).mp hmemD
  · rw [h]; exact zpow_mem_zpowers w i
  · exfalso
    have h1 : (s * w * s) * (s * w * s) = 1 := by rw [h]; exact hd.refl_sq i
    have h2 : w * w = 1 := by
      have hc := conj_involution_cancel hs2 (w * w)
      have e1 : s * (w * w) * s = (s * w * s) * (s * w * s) := by
        calc s * (w * w) * s = s * w * (s * s) * w * s := by rw [hs2]; group
          _ = (s * w * s) * (s * w * s) := by group
      rw [e1, h1] at hc
      rw [← hc]
      calc s * 1 * s = s * s := by rw [mul_one]
        _ = 1 := hs2
    have := orderOf_dvd_of_pow_eq_one (show w ^ 2 = 1 by rw [sq]; exact h2)
    rw [hd.order_w] at this
    have h3 : 2 ^ (e + 1) ≤ 2 := Nat.le_of_dvd (by norm_num) this
    have h4 : 4 ≤ 2 ^ (e + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem conj_zpow_rot {w s : G} (hs2 : s * s = 1) {κ : ℤ} (hκ : w ^ κ = s * w * s) (i : ℤ) :
    s * w ^ i * s = w ^ (κ * i) := by
  have h : s * w ^ i * s = (s * w * s) ^ i := by
    have := conj_zpow (a := s) (b := w) (i := i)
    rw [inv_eq_of_mul_eq_one_right hs2] at this
    exact this.symm
  rw [h, ← hκ, ← zpow_mul]

theorem conj_refl_eq {e : ℕ} {w t s : G} (hd : BareDatum e w t) (hs2 : s * s = 1)
    (hsn : ∀ d ∈ dsub w t, s * d * s ∈ dsub w t) {κ : ℤ} (hκ : w ^ κ = s * w * s) :
    ∃ a : ℤ, s * t * s = w ^ a * t := by
  obtain ⟨i, h | h⟩ := (hd.mem_dsub_iff).mp (hsn t (mem_sup_right (mem_zpowers t)))
  · exfalso
    apply hd.t_not_mem
    have ht : t = w ^ (κ * i) :=
      calc t = s * (s * t * s) * s := (conj_involution_cancel hs2 t).symm
        _ = s * w ^ i * s := by rw [h]
        _ = w ^ (κ * i) := conj_zpow_rot hs2 hκ i
    rw [ht]
    exact zpow_mem_zpowers w _
  · exact ⟨i, h⟩

theorem kappa_odd {e : ℕ} {w t s : G} (hd : BareDatum e w t) (hs2 : s * s = 1) {κ : ℤ}
    (hκ : w ^ κ = s * w * s) : Odd κ := by
  rcases Int.even_or_odd' κ with ⟨m, hm | hm⟩
  · exfalso
    have h1 : s * w ^ (2 ^ e) * s = 1 := by
      have := conj_zpow_rot hs2 hκ ((2 ^ e : ℕ) : ℤ)
      rw [zpow_natCast] at this
      rw [this, hm]
      have e1 : (2 * m * ((2 ^ e : ℕ) : ℤ)) = ((2 ^ (e + 1) : ℕ) : ℤ) * m := by push_cast; ring
      rw [e1, zpow_mul, zpow_natCast, hd.w_pow_order, one_zpow]
    apply hd.center_ne_one
    calc w ^ (2 ^ e) = s * (s * w ^ (2 ^ e) * s) * s := (conj_involution_cancel hs2 _).symm
      _ = 1 := by rw [h1, mul_one, hs2]
  · exact ⟨m, hm⟩

theorem conj_refl_zpow {w t s : G} (hs2 : s * s = 1) {κ a : ℤ} (hκ : w ^ κ = s * w * s)
    (ha : s * t * s = w ^ a * t) (i : ℤ) : s * (w ^ i * t) * s = w ^ (κ * i + a) * t := by
  have h1 : s * (w ^ i * t) * s = (s * w ^ i * s) * (s * t * s) := by
    calc s * (w ^ i * t) * s = s * w ^ i * (s * s) * t * s := by rw [hs2, mul_one]; group
      _ = (s * w ^ i * s) * (s * t * s) := by group
  rw [h1, conj_zpow_rot hs2 hκ, ha, ← mul_assoc, ← zpow_add]

theorem fixed_zpow_iff {e : ℕ} {w t s : G} (hd : BareDatum e w t) (hs2 : s * s = 1) {κ : ℤ}
    (hκ : w ^ κ = s * w * s) (N : ℤ) :
    s * w ^ N * s = w ^ N ↔ (2 : ℤ) ^ (e + 1) ∣ (κ - 1) * N := by
  rw [conj_zpow_rot hs2 hκ, hd.zpow_eq_zpow_iff]
  constructor <;> intro h <;> convert h using 1 <;> ring

theorem a_odd {e : ℕ} {w t s : G} (hd : BareDatum e w t) (hs2 : s * s = 1)
    (hfix : FixLeTwo s (dsub w t)) (he : 1 ≤ e) {κ a : ℤ} (hκ : w ^ κ = s * w * s)
    (ha : s * t * s = w ^ a * t) : Odd a := by
  rcases Int.even_or_odd' a with ⟨b, hb | hb⟩
  swap
  · exact ⟨b, hb⟩
  exfalso
  obtain ⟨m, hm⟩ := kappa_odd hd hs2 hκ
  obtain ⟨e₀, rfl⟩ : ∃ e₀, e = e₀ + 1 := ⟨e - 1, by omega⟩
  have h1D : (1 : G) ∈ dsub w t := one_mem _
  have h1fix : s * 1 * s = 1 := by rw [mul_one]; exact hs2
  have hcD : w ^ (2 ^ (e₀ + 1)) ∈ dsub w t := mem_sup_left (pow_mem (mem_zpowers w) _)
  have hc_fix : s * w ^ (2 ^ (e₀ + 1)) * s = w ^ (2 ^ (e₀ + 1)) := by
    have := (fixed_zpow_iff hd hs2 hκ ((2 ^ (e₀ + 1) : ℕ) : ℤ)).mpr
      ⟨m, by rw [hm]; push_cast; ring⟩
    rwa [zpow_natCast] at this
  have hm_odd : Odd m := by
    by_contra hnodd
    obtain ⟨n, hn⟩ := Int.not_odd_iff_even.mp hnodd
    have hrD : w ^ (2 ^ e₀) ∈ dsub w t := mem_sup_left (pow_mem (mem_zpowers w) _)
    have hr_fix : s * w ^ (2 ^ e₀) * s = w ^ (2 ^ e₀) := by
      have := (fixed_zpow_iff hd hs2 hκ ((2 ^ e₀ : ℕ) : ℤ)).mpr
        ⟨n, by rw [hm, hn]; push_cast; ring⟩
      rwa [zpow_natCast] at this
    have hr1 : w ^ (2 ^ e₀) ≠ 1 := by
      intro h
      have h2 := orderOf_dvd_of_pow_eq_one h
      rw [hd.order_w] at h2
      have h3 := Nat.le_of_dvd (by positivity) h2
      have h4 : 2 ^ e₀ < 2 ^ (e₀ + 1 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hrc : w ^ (2 ^ e₀) ≠ w ^ (2 ^ (e₀ + 1)) := by
      intro h
      apply hr1
      have h2 : w ^ (2 ^ (e₀ + 1)) = w ^ (2 ^ e₀) * w ^ (2 ^ e₀) := by
        rw [pow_succ, mul_two, pow_add]
      rw [h2] at h
      exact mul_eq_left.mp h.symm
    rcases hfix 1 h1D _ hrD _ hcD h1fix hr_fix hc_fix with h | h | h
    · exact hr1 h.symm
    · exact hd.center_ne_one h.symm
    · exact hrc h
  obtain ⟨i, q, hiq⟩ := exists_dvd_mul_add hm_odd (e₀ + 1) b
  have hu_fix : s * (w ^ i * t) * s = w ^ i * t := by
    rw [conj_refl_zpow hs2 hκ ha i]
    congr 1
    rw [hd.zpow_eq_zpow_iff]
    exact ⟨q, by rw [hm, hb]; linear_combination 2 * hiq⟩
  have huD : w ^ i * t ∈ dsub w t := (hd.mem_dsub_iff).mpr ⟨i, Or.inr rfl⟩
  have huc : w ^ i * t ≠ w ^ (2 ^ (e₀ + 1)) := by
    intro h
    apply hd.t_not_mem
    have : t = (w ^ i)⁻¹ * w ^ (2 ^ (e₀ + 1)) := by rw [← h]; group
    rw [this]
    exact mul_mem (inv_mem (zpow_mem_zpowers w i)) (pow_mem (mem_zpowers w) _)
  rcases hfix 1 h1D _ huD _ hcD h1fix hu_fix hc_fix with h | h | h
  · exact hd.refl_ne_one i h.symm
  · exact hd.center_ne_one h.symm
  · exact huc h

theorem orderOf_mul_refl {e : ℕ} {w t s : G} (hd : BareDatum e w t) (hs2 : s * s = 1)
    (hsn : ∀ d ∈ dsub w t, s * d * s ∈ dsub w t) (hfix : FixLeTwo s (dsub w t)) (he : 1 ≤ e) :
    orderOf (t * s) = 2 ^ (e + 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨κ, hκ⟩ := mem_zpowers_iff.mp (conj_rot_mem hd hs2 hsn he)
  obtain ⟨a, ha⟩ := conj_refl_eq hd hs2 hsn hκ
  have hao := a_odd hd hs2 hfix he hκ ha
  have hsq : (t * s) ^ 2 = w ^ (-a) := by
    calc (t * s) ^ 2 = t * (s * t * s) := by rw [sq]; group
      _ = t * (w ^ a * t) := by rw [ha]
      _ = (t * w ^ a) * t := by rw [mul_assoc]
      _ = (w ^ (-a) * t) * t := by rw [hd.t_zpow]
      _ = w ^ (-a) := by rw [mul_assoc, hd.t_sq, mul_one]
  have hnot : ¬ (t * s) ^ (2 ^ (e + 1)) = 1 := by
    have h1 : (t * s) ^ (2 ^ (e + 1)) = w ^ (-a * ((2 ^ e : ℕ) : ℤ)) := by
      rw [pow_succ', pow_mul, hsq, ← zpow_natCast, ← zpow_mul]
    intro h
    rw [h1, hd.zpow_eq_one_iff] at h
    obtain ⟨c, hc⟩ := h
    have h2 : (-a) * (2 : ℤ) ^ e = (2 * c) * (2 : ℤ) ^ e := by
      push_cast at hc
      rw [hc]; ring
    have h3 : -a = 2 * c := mul_right_cancel₀ (pow_ne_zero e (by norm_num)) h2
    obtain ⟨k, hk⟩ := hao
    omega
  have hfin : (t * s) ^ (2 ^ (e + 1 + 1)) = 1 := by
    rw [pow_succ', pow_mul, hsq, ← zpow_natCast, ← zpow_mul, hd.zpow_eq_one_iff]
    exact ⟨-a, by push_cast; ring⟩
  exact orderOf_eq_prime_pow hnot hfin

theorem exists_reflection_order_zero {w t s : G} (hd : BareDatum 0 w t) (hs2 : s * s = 1)
    (hsn : ∀ d ∈ dsub w t, s * d * s ∈ dsub w t) (hfix : FixLeTwo s (dsub w t)) :
    ∃ t₀ ∈ dsub w t, t₀ * t₀ = 1 ∧ orderOf (t₀ * s) = 2 ^ (0 + 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw2 : w * w = 1 := by simpa [sq] using hd.w_pow_order
  have hwD : w ∈ dsub w t := mem_sup_left (mem_zpowers w)
  have htD : t ∈ dsub w t := mem_sup_right (mem_zpowers t)
  have hw1 : w ≠ 1 := by
    intro h
    have := hd.order_w
    rw [h, orderOf_one] at this
    omega
  have ht1 : t ≠ 1 := fun h => hd.t_not_mem (h ▸ one_mem _)
  have hwt : w ≠ t := fun h => hd.t_not_mem (h ▸ mem_zpowers w)
  have hD2 : ∀ g ∈ dsub w t, g * g = 1 := by
    intro g hg
    obtain ⟨i, rfl | rfl⟩ := (hd.mem_dsub_iff).mp hg
    · rw [← zpow_add]
      exact (hd.zpow_eq_one_iff).mpr ⟨i, by ring⟩
    · exact hd.refl_sq i
  have key : ∀ t₀ ∈ dsub w t, t₀ * t₀ = 1 → s * t₀ * s ≠ t₀ → orderOf (t₀ * s) = 2 ^ (0 + 2) := by
    intro t₀ ht₀ ht₀2 hnf
    have hsq : (t₀ * s) ^ 2 = t₀ * (s * t₀ * s) := by rw [sq]; group
    have hD : t₀ * (s * t₀ * s) ∈ dsub w t := mul_mem ht₀ (hsn t₀ ht₀)
    have hnot : ¬ (t₀ * s) ^ (2 ^ 1) = 1 := by
      intro h
      rw [pow_one, hsq] at h
      apply hnf
      calc s * t₀ * s = t₀ * (t₀ * (s * t₀ * s)) := by rw [← mul_assoc, ht₀2, one_mul]
        _ = t₀ := by rw [h, mul_one]
    have hfin : (t₀ * s) ^ (2 ^ (1 + 1)) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hsq]
      exact (sq _).trans (hD2 _ hD)
    exact orderOf_eq_prime_pow hnot hfin
  by_cases hwfix : s * w * s = w
  · by_cases htfix : s * t * s = t
    · exfalso
      rcases hfix 1 (one_mem _) w hwD t htD (by rw [mul_one]; exact hs2) hwfix htfix with
        h | h | h
      · exact hw1 h.symm
      · exact ht1 h.symm
      · exact hwt h
    · exact ⟨t, htD, hd.t_sq, key t htD hd.t_sq htfix⟩
  · exact ⟨w, hwD, hw2, key w hwD hw2 hwfix⟩

theorem exists_datum_succ (hconj : ∀ g u, u ∈ 𝒞 → g * u * g⁻¹ ∈ 𝒞) {e : ℕ} {w t : G}
    (hd : Datum 𝒞 e w t) {s : G} (hs𝒞 : s ∈ 𝒞) (hs2 : s * s = 1)
    (hsn : ∀ d ∈ dsub w t, s * d * s ∈ dsub w t) (hfix : FixLeTwo s (dsub w t)) :
    ∃ w' t' : G, Datum 𝒞 (e + 1) w' t' := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · obtain ⟨t₀, ht₀, ht₀2, hord⟩ := exists_reflection_order_zero hd.toBareDatum hs2 hsn hfix
    exact ⟨_, _, datum_extend hconj hd hs𝒞 hs2 hsn ht₀ ht₀2 hord⟩
  · have hord := orderOf_mul_refl hd.toBareDatum hs2 hsn hfix he
    exact ⟨_, _, datum_extend hconj hd hs𝒞 hs2 hsn (mem_sup_right (mem_zpowers t))
      hd.t_sq hord⟩

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof
