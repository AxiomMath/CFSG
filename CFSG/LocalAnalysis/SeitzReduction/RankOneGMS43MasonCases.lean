module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace GMS43

variable {P : Type*} [Group P]

theorem rho_mul_self_and_ne_one {w ρ : P} {m : ℕ} (hm : 1 ≤ m) (hw : orderOf w = 2 ^ m)
    (hρ : w ^ (2 ^ (m - 1)) = ρ) : ρ * ρ = 1 ∧ ρ ≠ 1 := by
  constructor
  · rw [← hρ, ← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hm, ← hw,
      pow_orderOf_eq_one]
  · rw [← hρ]
    apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [hw]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem zpow_eq_of_mul_self {ρ : P} (hρ2 : ρ * ρ = 1) (k : ℤ) :
    (Even k → ρ ^ k = 1) ∧ (Odd k → ρ ^ k = ρ) := by
  constructor
  · rintro ⟨l, rfl⟩
    rw [← two_mul, zpow_mul, zpow_two, hρ2, one_zpow]
  · rintro ⟨l, rfl⟩
    rw [zpow_add_one, zpow_mul, zpow_two, hρ2, one_zpow, one_mul]

theorem zpow_eq_one_or_eq_of_mul_self {w ρ : P} {m : ℕ} (hm : 1 ≤ m) (hw : orderOf w = 2 ^ m)
    (hρ : w ^ (2 ^ (m - 1)) = ρ) {i : ℤ} (hi : w ^ i * w ^ i = 1) : w ^ i = 1 ∨ w ^ i = ρ := by
  have h1 : w ^ (2 * i) = 1 := by rw [two_mul, zpow_add, hi]
  rw [← orderOf_dvd_iff_zpow_eq_one, hw] at h1
  have h2 : ((2 ^ (m - 1) : ℕ) : ℤ) ∣ i := by
    have h3 : ((2 ^ m : ℕ) : ℤ) = 2 * ((2 ^ (m - 1) : ℕ) : ℤ) := by
      have h4 : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ', Nat.sub_add_cancel hm]
      rw [h4]
      push_cast
      ring
    rw [h3] at h1
    exact Int.dvd_of_mul_dvd_mul_left (by norm_num) h1
  obtain ⟨k, rfl⟩ := h2
  rw [zpow_mul, zpow_natCast, hρ]
  have hρ2 := (rho_mul_self_and_ne_one hm hw hρ).1
  rcases Int.even_or_odd k with hk | hk
  · exact Or.inl ((zpow_eq_of_mul_self hρ2 k).1 hk)
  · exact Or.inr ((zpow_eq_of_mul_self hρ2 k).2 hk)

theorem le_two_of_pow_four {w : P} {m : ℕ} (hw : orderOf w = 2 ^ m) (h : w ^ 4 = 1) : m ≤ 2 := by
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [hw, show (4 : ℕ) = 2 ^ 2 by norm_num] at h1
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1

theorem zpow_mul_conj_zpow_eq_one {j j₁ w : P} {s : ℤ} (hj : j * j = 1) (hj₁ : j₁ * j₁ = 1)
    (hs : j * j₁ * (j * j₁) = w ^ s) : w ^ s * (j₁ * w * j₁⁻¹) ^ s = 1 := by
  have hj₁inv : j₁⁻¹ = j₁ := inv_eq_of_mul_eq_one_right hj₁
  have hjj : ∀ x : P, j * (j * x) = x := fun x => by rw [← mul_assoc, hj, one_mul]
  have hj₁j₁ : ∀ x : P, j₁ * (j₁ * x) = x := fun x => by rw [← mul_assoc, hj₁, one_mul]
  rw [conj_zpow, ← hs, hj₁inv]
  simp only [mul_assoc, hjj, hj₁j₁, hj₁]

theorem eq_mul_of_mul_self_eq {j ρ y c : P}
    (hC : ∀ a b : P, a * j = j * a → b * j = j * b → a * b = b * a)
    (hinv' : ∀ v : P, v * j = j * v → v * v = 1 → v = 1 ∨ v = j ∨ v = ρ ∨ v = j * ρ)
    (hy : y * j = j * y) (hc : c * j = j * c) (hyc : y * y = c * c) :
    y = c ∨ y = c * j ∨ y = c * ρ ∨ y = c * (j * ρ) := by
  have hcinv : c⁻¹ * j = j * c⁻¹ := by
    calc c⁻¹ * j = c⁻¹ * (j * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * j) * c⁻¹ := by rw [hc]
      _ = j * c⁻¹ := by group
  have hv : c⁻¹ * y * j = j * (c⁻¹ * y) := by
    rw [mul_assoc, hy, ← mul_assoc, hcinv, mul_assoc]
  have hvv : c⁻¹ * y * (c⁻¹ * y) = 1 := by
    calc c⁻¹ * y * (c⁻¹ * y) = c⁻¹ * (y * c⁻¹) * y := by group
      _ = c⁻¹ * (c⁻¹ * y) * y := by rw [hC y c⁻¹ hy hcinv]
      _ = c⁻¹ * c⁻¹ * (y * y) := by group
      _ = 1 := by rw [hyc]; group
  have key : ∀ v, c⁻¹ * y = v → y = c * v := fun v hv' => by rw [← hv']; group
  rcases hinv' _ hv hvv with h | h | h | h
  · left; rw [key _ h, mul_one]
  · exact Or.inr (Or.inl (key _ h))
  · exact Or.inr (Or.inr (Or.inl (key _ h)))
  · exact Or.inr (Or.inr (Or.inr (key _ h)))

theorem le_one_of_pow_two {w : P} {m : ℕ} (hw : orderOf w = 2 ^ m) (h : w ^ 2 = 1) : m ≤ 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [hw, show (2 : ℕ) = 2 ^ 1 by norm_num] at h1
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1

theorem mul_comm_of_mul_mul_eq_one {j j₁ : P} (hj : j * j = 1) (hj₁ : j₁ * j₁ = 1)
    (h : j * j₁ * (j * j₁) = 1) : j * j₁ = j₁ * j := by
  have h1 := inv_eq_of_mul_eq_one_right h
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hj, inv_eq_of_mul_eq_one_right hj₁] at h1
  exact h1.symm

theorem inv_eq_mul_of_mul_self_eq {x ρ : P} (hx : x * x = ρ) (hρ2 : ρ * ρ = 1) :
    x⁻¹ = x * ρ :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hx, hρ2])

theorem orderOf_mul_eq_of_conj_eq_inv {j j₁ w ρ : P} {m : ℕ} {s : ℤ} (hm : 1 ≤ m)
    (hj : j * j = 1) (hj₁ : j₁ * j₁ = 1) (hw : orderOf w = 2 ^ m)
    (hρ : w ^ (2 ^ (m - 1)) = ρ) (hjw : j * w * j⁻¹ = w⁻¹) (he : j₁ * w * j₁⁻¹ = w⁻¹)
    (hs : j * j₁ * (j * j₁) = w ^ s)
    (hinv' : ∀ v : P, v * j = j * v → v * v = 1 → v = 1 ∨ v = j ∨ v = ρ ∨ v = j * ρ)
    (hnc : j * j₁ ≠ j₁ * j) (hnot : ∀ i : ℤ, j₁ ≠ j * w ^ i) :
    orderOf (j * j₁) = 2 ^ (m + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  have hj₁inv : j₁⁻¹ = j₁ := inv_eq_of_mul_eq_one_right hj₁
  obtain ⟨hρ2, hρ1⟩ := rho_mul_self_and_ne_one hm hw hρ
  have hjwz : ∀ n : ℤ, j * w ^ n * j⁻¹ = w ^ (-n) := fun n => by
    rw [← conj_zpow, hjw, inv_zpow, zpow_neg]
  have hnotw : ∀ a : ℤ, j₁ ≠ w ^ a := by
    intro a ha
    apply hnc
    have h1 : j * j₁ * j⁻¹ = j₁ := by rw [ha, hjwz, zpow_neg, ← ha, hj₁inv]
    calc j * j₁ = j * j₁ * j⁻¹ * j := by group
      _ = j₁ * j := by rw [h1]
  have hρw : ρ = w ^ ((2 : ℤ) ^ (m - 1)) := by
    rw [← hρ, ← zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  set r := j * j₁ with hr
  have hj₁r : j₁ = j * r := by rw [hr, ← mul_assoc, hj, one_mul]
  have hjr : j * r * j⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hjinv, hj₁inv]
    calc j * (j * j₁) * j = (j * j) * j₁ * j := by group
      _ = j₁ * j := by rw [hj, one_mul]
  have hsodd : Odd s := by
    obtain ⟨t, hst | hst⟩ := Int.even_or_odd' s
    · exfalso
      have hrw : Commute r w := by
        have h1 : r * w * r⁻¹ = w := by
          rw [hr, show j * j₁ * w * (j * j₁)⁻¹ = j * (j₁ * w * j₁⁻¹) * j⁻¹ by group, he,
            show j * w⁻¹ * j⁻¹ = (j * w * j⁻¹)⁻¹ by group, hjw, inv_inv]
        calc r * w = r * w * r⁻¹ * r := by group
          _ = w * r := by rw [h1]
      set y := r * w ^ (-t) with hy
      have hyy : y * y = 1 := by
        calc y * y = r * (w ^ (-t) * r) * w ^ (-t) := by rw [hy]; group
          _ = r * r * (w ^ (-t) * w ^ (-t)) := by
              rw [← (hrw.zpow_right (-t)).eq]; group
          _ = 1 := by
              rw [hs, hst, ← zpow_add, ← zpow_add, show 2 * t + (-t + -t) = 0 by ring,
                zpow_zero]
      have hyj : y * j = j * y := by
        have h1 : j * y * j⁻¹ = y⁻¹ := by
          rw [hy, show j * (r * w ^ (-t)) * j⁻¹ = (j * r * j⁻¹) * (j * w ^ (-t) * j⁻¹) by group,
            hjr, hjwz, neg_neg, mul_inv_rev r (w ^ (-t)), ← zpow_neg, neg_neg]
          exact (hrw.inv_left.zpow_right t).eq
        rw [inv_eq_of_mul_eq_one_right hyy] at h1
        calc y * j = j * y * j⁻¹ * j := by rw [h1]
          _ = j * y := by group
      have hr' : ∀ v : P, y = v → r = v * w ^ t := fun v hv => by
        rw [← hv, hy, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
      rcases hinv' y hyj hyy with h | h | h | h
      · apply hnot t
        rw [hj₁r, hr' 1 h, one_mul]
      · apply hnotw t
        rw [hj₁r, hr' j h, ← mul_assoc, hj, one_mul]
      · apply hnot (2 ^ (m - 1) + t)
        rw [hj₁r, hr' ρ h, hρw, ← zpow_add]
      · apply hnotw (2 ^ (m - 1) + t)
        rw [hj₁r, hr' (j * ρ) h, ← mul_assoc, ← mul_assoc, hj, one_mul, hρw, ← zpow_add]
    · exact ⟨t, hst⟩
  have hr2m : r ^ (2 ^ m) = ρ := by
    have h1 : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ', Nat.sub_add_cancel hm]
    rw [h1, pow_mul, pow_two, hs, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hρ]
    exact (zpow_eq_of_mul_self hρ2 s).2 hsodd
  apply orderOf_eq_prime_pow
  · rw [hr2m]
    exact hρ1
  · rw [pow_succ, pow_mul, hr2m, pow_two, hρ2]

theorem false_of_conj_eq_self {j j₁ w w' ρ : P} {m : ℕ} {s : ℤ} (hm : 2 ≤ m)
    (hj : j * j = 1) (hj₁ : j₁ * j₁ = 1) (hw : orderOf w = 2 ^ m) (hw' : orderOf w' = 2 ^ m)
    (hρ : w ^ (2 ^ (m - 1)) = ρ) (hρ' : w' ^ (2 ^ (m - 1)) = ρ) (hρc : ∀ x : P, x * ρ = ρ * x)
    (hww' : w * w' = w' * w) (hjw : j * w * j⁻¹ = w⁻¹) (hj₁w' : j₁ * w' * j₁⁻¹ = w'⁻¹)
    (he : j₁ * w * j₁⁻¹ = w) (he' : j * w' * j⁻¹ = w') (hs : j * j₁ * (j * j₁) = w ^ s)
    (hC : ∀ a b : P, a * j = j * a → b * j = j * b → a * b = b * a)
    (hinv' : ∀ v : P, v * j = j * v → v * v = 1 → v = 1 ∨ v = j ∨ v = ρ ∨ v = j * ρ)
    (hnc : j * j₁ ≠ j₁ * j) : False := by
  have hm1 : 1 ≤ m := by omega
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  have hj₁inv : j₁⁻¹ = j₁ := inv_eq_of_mul_eq_one_right hj₁
  obtain ⟨hρ2, -⟩ := rho_mul_self_and_ne_one hm1 hw hρ
  have hr2 : j * j₁ * (j * j₁) = ρ := by
    have h1 := zpow_mul_conj_zpow_eq_one hj hj₁ hs
    rw [he] at h1
    rcases zpow_eq_one_or_eq_of_mul_self hm1 hw hρ h1 with h | h
    · exact absurd (mul_comm_of_mul_mul_eq_one hj hj₁ (by rw [hs, h])) hnc
    · rw [hs, h]
  have hrw : j * j₁ * w * (j * j₁)⁻¹ = w⁻¹ := by
    rw [show j * j₁ * w * (j * j₁)⁻¹ = j * (j₁ * w * j₁⁻¹) * j⁻¹ by group, he, hjw]
  have hrw' : j * j₁ * w' * (j * j₁)⁻¹ = w'⁻¹ := by
    rw [show j * j₁ * w' * (j * j₁)⁻¹ = j * (j₁ * w' * j₁⁻¹) * j⁻¹ by group, hj₁w',
      show j * w'⁻¹ * j⁻¹ = (j * w' * j⁻¹)⁻¹ by group, he']
  have hjr : j * (j * j₁) * j⁻¹ = (j * j₁)⁻¹ := by
    rw [mul_inv_rev, hjinv, hj₁inv]
    calc j * (j * j₁) * j = (j * j) * j₁ * j := by group
      _ = j₁ * j := by rw [hj, one_mul]
  set r := j * j₁ with hr
  set q := w ^ (2 ^ (m - 2)) with hq
  have hqq : q * q = ρ := by
    rw [hq, ← pow_add, ← two_mul, ← pow_succ', show m - 2 + 1 = m - 1 by omega, hρ]
  have hjq : j * q * j⁻¹ = q⁻¹ := by rw [hq, ← conj_pow, hjw, inv_pow]
  have hrq : r * q * r⁻¹ = q⁻¹ := by rw [hq, ← conj_pow, hrw, inv_pow]
  have hqinv := inv_eq_mul_of_mul_self_eq hqq hρ2
  have hrinv := inv_eq_mul_of_mul_self_eq hr2 hρ2
  have hyy : q * r * (q * r) = ρ := by
    calc q * r * (q * r) = q * (r * q * r⁻¹) * (r * r) := by group
      _ = ρ := by rw [hrq, hr2]; group
  have hyj : q * r * j = j * (q * r) := by
    have h1 : j * (q * r) * j⁻¹ = q * r := by
      rw [show j * (q * r) * j⁻¹ = (j * q * j⁻¹) * (j * r * j⁻¹) by group, hjq, hjr, hqinv,
        hrinv, mul_assoc q ρ, ← mul_assoc ρ r ρ, ← hρc r, mul_assoc r ρ ρ, hρ2, mul_one]
    calc q * r * j = j * (q * r) * j⁻¹ * j := by rw [h1]
      _ = j * (q * r) := by group
  set c := w' ^ (2 ^ (m - 2)) with hc
  have hcc : c * c = ρ := by
    rw [hc, ← pow_add, ← two_mul, ← pow_succ', show m - 2 + 1 = m - 1 by omega, hρ']
  have hcj : c * j = j * c := by
    have h1 : j * c * j⁻¹ = c := by rw [hc, ← conj_pow, he']
    calc c * j = j * c * j⁻¹ * j := by rw [h1]
      _ = j * c := by group
  have hjw'c : Commute j w' := by
    calc j * w' = j * w' * j⁻¹ * j := by group
      _ = w' * j := by rw [he']
  have hcw' : Commute c w' := (Commute.refl w').pow_left _
  have hρw' : Commute ρ w' := (hρc w').symm
  have hyw' : Commute (q * r) w' := by
    rcases eq_mul_of_mul_self_eq hC hinv' hyj hcj (by rw [hyy, hcc]) with h | h | h | h <;>
      rw [h]
    · exact hcw'
    · exact hcw'.mul_left hjw'c
    · exact hcw'.mul_left hρw'
    · exact hcw'.mul_left (hjw'c.mul_left hρw')
  have hqw' : Commute q w' := Commute.pow_left hww' _
  have h1 : q * r * w' * (q * r)⁻¹ = w'⁻¹ := by
    rw [show q * r * w' * (q * r)⁻¹ = q * (r * w' * r⁻¹) * q⁻¹ by group, hrw',
      (hqw'.inv_right).eq, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : q * r * w' * (q * r)⁻¹ = w' := by
    rw [hyw'.eq, mul_assoc, mul_inv_cancel, mul_one]
  have h3 : w' ^ 2 = 1 := by
    rw [pow_two]
    calc w' * w' = w' * w'⁻¹ := by rw [h1.symm.trans h2]
      _ = 1 := mul_inv_cancel w'
  have := le_one_of_pow_two hw' h3
  omega

theorem false_of_conj_eq_mul {j j₁ w w' ρ : P} {m : ℕ} {s : ℤ} (hm : 3 ≤ m)
    (hj : j * j = 1) (hj₁ : j₁ * j₁ = 1) (hw : orderOf w = 2 ^ m) (hw' : orderOf w' = 2 ^ m)
    (hρ : w ^ (2 ^ (m - 1)) = ρ) (hρ' : w' ^ (2 ^ (m - 1)) = ρ) (hρc : ∀ x : P, x * ρ = ρ * x)
    (hww' : w * w' = w' * w) (hjw : j * w * j⁻¹ = w⁻¹) (hj₁w' : j₁ * w' * j₁⁻¹ = w'⁻¹)
    (he : j₁ * w * j₁⁻¹ = w * ρ) (he' : j * w' * j⁻¹ = w' * ρ) (hs : j * j₁ * (j * j₁) = w ^ s)
    (hC : ∀ a b : P, a * j = j * a → b * j = j * b → a * b = b * a)
    (hinv' : ∀ v : P, v * j = j * v → v * v = 1 → v = 1 ∨ v = j ∨ v = ρ ∨ v = j * ρ)
    (hnc : j * j₁ ≠ j₁ * j) : False := by
  have hm1 : 1 ≤ m := by omega
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  have hj₁inv : j₁⁻¹ = j₁ := inv_eq_of_mul_eq_one_right hj₁
  obtain ⟨hρ2, -⟩ := rho_mul_self_and_ne_one hm1 hw hρ
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hjρ : j * ρ * j⁻¹ = ρ := by rw [hρc j, mul_assoc, mul_inv_cancel, mul_one]
  have hρpow : ρ ^ (2 ^ (m - 2)) = 1 := by
    rw [show 2 ^ (m - 2) = 2 * 2 ^ (m - 3) by rw [← pow_succ']; congr 1; omega, pow_mul,
      pow_two, hρ2, one_pow]
  have hr2 : j * j₁ * (j * j₁) = ρ := by
    have h1 := zpow_mul_conj_zpow_eq_one hj hj₁ hs
    rw [he, Commute.mul_zpow (hρc w)] at h1
    rcases Int.even_or_odd s with hse | hso
    · rw [(zpow_eq_of_mul_self hρ2 s).1 hse, mul_one] at h1
      rcases zpow_eq_one_or_eq_of_mul_self hm1 hw hρ h1 with h | h
      · exact absurd (mul_comm_of_mul_mul_eq_one hj hj₁ (by rw [hs, h])) hnc
      · rw [hs, h]
    · exfalso
      rw [(zpow_eq_of_mul_self hρ2 s).2 hso] at h1
      have h3 : w ^ s * w ^ s = ρ := by
        calc w ^ s * w ^ s = w ^ s * (w ^ s * ρ) * ρ⁻¹ := by group
          _ = ρ := by rw [h1, one_mul, hρinv]
      have h2 : w ^ (4 * s) = 1 := by
        rw [show 4 * s = s + s + (s + s) by ring, zpow_add, zpow_add, h3]
        exact hρ2
      rw [← orderOf_dvd_iff_zpow_eq_one, hw] at h2
      have h8 : (8 : ℤ) ∣ ((2 ^ m : ℕ) : ℤ) := by
        have h9 : (2 : ℕ) ^ m = 8 * 2 ^ (m - 3) := by
          rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
          congr 1
          omega
        rw [h9]
        push_cast
        exact dvd_mul_right 8 _
      obtain ⟨t, rfl⟩ := hso
      have := dvd_trans h8 h2
      omega
  have hrw : j * j₁ * w * (j * j₁)⁻¹ = w⁻¹ * ρ := by
    rw [show j * j₁ * w * (j * j₁)⁻¹ = j * (j₁ * w * j₁⁻¹) * j⁻¹ by group, he,
      show j * (w * ρ) * j⁻¹ = (j * w * j⁻¹) * (j * ρ * j⁻¹) by group, hjw, hjρ]
  have hrw' : j * j₁ * w' * (j * j₁)⁻¹ = w'⁻¹ * ρ := by
    rw [show j * j₁ * w' * (j * j₁)⁻¹ = j * (j₁ * w' * j₁⁻¹) * j⁻¹ by group, hj₁w',
      show j * w'⁻¹ * j⁻¹ = (j * w' * j⁻¹)⁻¹ by group, he', mul_inv_rev, hρinv]
    exact (hρc _).symm
  have hjr : j * (j * j₁) * j⁻¹ = (j * j₁)⁻¹ := by
    rw [mul_inv_rev, hjinv, hj₁inv]
    calc j * (j * j₁) * j = (j * j) * j₁ * j := by group
      _ = j₁ * j := by rw [hj, one_mul]
  set r := j * j₁ with hr
  set q := w ^ (2 ^ (m - 2)) with hq
  have hqq : q * q = ρ := by
    rw [hq, ← pow_add, ← two_mul, ← pow_succ', show m - 2 + 1 = m - 1 by omega, hρ]
  have hjq : j * q * j⁻¹ = q⁻¹ := by rw [hq, ← conj_pow, hjw, inv_pow]
  have hrq : r * q * r⁻¹ = q⁻¹ := by
    rw [hq, ← conj_pow, hrw, Commute.mul_pow (hρc w⁻¹), hρpow, mul_one, inv_pow]
  have hqinv := inv_eq_mul_of_mul_self_eq hqq hρ2
  have hrinv := inv_eq_mul_of_mul_self_eq hr2 hρ2
  have hyy : q * r * (q * r) = ρ := by
    calc q * r * (q * r) = q * (r * q * r⁻¹) * (r * r) := by group
      _ = ρ := by rw [hrq, hr2]; group
  have hyj : q * r * j = j * (q * r) := by
    have h1 : j * (q * r) * j⁻¹ = q * r := by
      rw [show j * (q * r) * j⁻¹ = (j * q * j⁻¹) * (j * r * j⁻¹) by group, hjq, hjr, hqinv,
        hrinv, mul_assoc q ρ, ← mul_assoc ρ r ρ, ← hρc r, mul_assoc r ρ ρ, hρ2, mul_one]
    calc q * r * j = j * (q * r) * j⁻¹ * j := by rw [h1]
      _ = j * (q * r) := by group
  set c := w' ^ (2 ^ (m - 2)) with hc
  have hcc : c * c = ρ := by
    rw [hc, ← pow_add, ← two_mul, ← pow_succ', show m - 2 + 1 = m - 1 by omega, hρ']
  have hcj : c * j = j * c := by
    have h1 : j * c * j⁻¹ = c := by
      rw [hc, ← conj_pow, he', Commute.mul_pow (hρc w'), hρpow, mul_one]
    calc c * j = j * c * j⁻¹ * j := by rw [h1]
      _ = j * c := by group
  have hcw' : Commute c w' := (Commute.refl w').pow_left _
  have hcρ : Commute c ρ := hρc c
  have hρw' : Commute ρ w' := (hρc w').symm
  have hqw' : Commute q w' := Commute.pow_left hww' _
  have h1 : q * r * w' * (q * r)⁻¹ = w'⁻¹ * ρ := by
    rw [show q * r * w' * (q * r)⁻¹ = q * (r * w' * r⁻¹) * q⁻¹ by group, hrw',
      ((hqw'.inv_right).mul_right (hρc q)).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hcw'ρ : c * (w' * ρ) * c⁻¹ = w' * ρ := by
    rw [(hcw'.mul_right hcρ).eq, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : q * r * w' * (q * r)⁻¹ = w' ∨ q * r * w' * (q * r)⁻¹ = w' * ρ := by
    rcases eq_mul_of_mul_self_eq hC hinv' hyj hcj (by rw [hyy, hcc]) with h | h | h | h <;>
      rw [h]
    · left
      rw [hcw'.eq, mul_assoc, mul_inv_cancel, mul_one]
    · right
      calc c * j * w' * (c * j)⁻¹ = c * (j * w' * j⁻¹) * c⁻¹ := by group
        _ = w' * ρ := by rw [he', hcw'ρ]
    · left
      calc c * ρ * w' * (c * ρ)⁻¹ = c * (ρ * w' * ρ⁻¹) * c⁻¹ := by group
        _ = w' := by rw [hρw'.eq, mul_assoc w' ρ, mul_inv_cancel, mul_one, hcw'.eq, mul_assoc,
          mul_inv_cancel, mul_one]
    · right
      calc c * (j * ρ) * w' * (c * (j * ρ))⁻¹ = c * (j * (ρ * w' * ρ⁻¹) * j⁻¹) * c⁻¹ := by group
        _ = w' * ρ := by
          rw [hρw'.eq, mul_assoc w' ρ, mul_inv_cancel, mul_one, he', hcw'ρ]
  have h4 : w' ^ 4 = 1 := by
    rcases h2 with h2 | h2 <;> rw [h1] at h2
    ·
      have h5 : w' * w' = ρ := by
        calc w' * w' = w' * (w'⁻¹ * ρ) := by rw [h2]
          _ = ρ := by group
      rw [show 4 = 2 + 2 by norm_num, pow_add, pow_two, h5, hρ2]
    ·
      have h5 : w' * w' = 1 := by
        have h6 : w'⁻¹ = w' := mul_right_cancel h2
        calc w' * w' = w' * w'⁻¹ := by rw [h6]
          _ = 1 := mul_inv_cancel w'
      rw [show 4 = 2 + 2 by norm_num, pow_add, pow_two, h5, one_mul]
  have := le_two_of_pow_four hw' h4
  omega

theorem exists_pow_two_eq_zpow {j w w' ρ : P} {m : ℕ} (hm : 2 ≤ m) (hw : orderOf w = 2 ^ m)
    (hρ : w ^ (2 ^ (m - 1)) = ρ) (hρ' : w' ^ (2 ^ (m - 1)) = ρ) (hρc : ∀ x : P, x * ρ = ρ * x)
    (hww' : w * w' = w' * w) (hjw : j * w * j⁻¹ = w⁻¹) (he' : j * w' * j⁻¹ = w'⁻¹ * ρ)
    (hinv' : ∀ v : P, v * j = j * v → v * v = 1 → v = 1 ∨ v = j ∨ v = ρ ∨ v = j * ρ) :
    ∃ a : ℤ, w' ^ 2 = (w ^ 2) ^ a := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hρ2, -⟩ := rho_mul_self_and_ne_one hm1 hw hρ
  have hjw1 : ¬ Commute j w := by
    intro h
    have h1 : w⁻¹ = w := by rw [← hjw, h.eq, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : w ^ 2 = 1 := by
      rw [pow_two]
      calc w * w = w * w⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel w
    have := le_one_of_pow_two hw h2
    omega
  have hΩ : ∀ v : P, Commute v w → v * j = j * v → v * v = 1 → v = 1 ∨ v = ρ := by
    intro v hvw hvj hvv
    rcases hinv' v hvj hvv with h | h | h | h
    · exact Or.inl h
    · rw [h] at hvw
      exact absurd hvw hjw1
    · exact Or.inr h
    · exfalso
      apply hjw1
      rw [h] at hvw
      have h1 : Commute (j * ρ * ρ) w := hvw.mul_left (hρc w).symm
      rwa [mul_assoc, hρ2, mul_one] at h1
  have key : ∀ d i : ℕ, 1 ≤ i → i + d = m - 1 → ∃ a : ℤ, w' ^ (2 ^ i) = (w ^ (2 ^ i)) ^ a := by
    intro d
    induction d with
    | zero =>
      intro i _ hi
      refine ⟨1, ?_⟩
      rw [zpow_one, show i = m - 1 by omega, hρ, hρ']
    | succ d ih =>
      intro i hi1 hi
      obtain ⟨a, ha⟩ := ih (i + 1) (by omega) (by omega)
      have hXX : w' ^ (2 ^ i) * w' ^ (2 ^ i) = (w ^ (2 ^ i) * w ^ (2 ^ i)) ^ a := by
        rw [← pow_add, ← pow_add, ← two_mul, ← pow_succ', ha]
      have hρi : ρ ^ (2 ^ i) = 1 := by
        rw [show 2 ^ i = 2 * 2 ^ (i - 1) by rw [← pow_succ']; congr 1; omega, pow_mul,
          pow_two, hρ2, one_pow]
      have hρW : (w ^ (2 ^ i)) ^ (2 ^ (d + 1)) = ρ := by
        rw [← pow_mul, ← pow_add, hi, hρ]
      set X := w' ^ (2 ^ i) with hX
      set W := w ^ (2 ^ i) with hW
      have hXw : Commute X w := Commute.pow_left (Commute.symm hww') _
      have hWw : Commute W w := (Commute.refl w).pow_left _
      have hXW : Commute X W := Commute.pow_right (Commute.pow_left (Commute.symm hww') _) _
      have hjX : j * X * j⁻¹ = X⁻¹ := by
        rw [hX, ← conj_pow, he', Commute.mul_pow (hρc w'⁻¹), hρi, mul_one, inv_pow]
      have hjW : j * W * j⁻¹ = W⁻¹ := by rw [hW, ← conj_pow, hjw, inv_pow]
      have hvw : Commute (X * W ^ (-a)) w := hXw.mul_left (hWw.zpow_left (-a))
      have hvv : X * W ^ (-a) * (X * W ^ (-a)) = 1 := by
        calc X * W ^ (-a) * (X * W ^ (-a)) = X * (W ^ (-a) * X) * W ^ (-a) := by group
          _ = X * X * (W ^ (-a) * W ^ (-a)) := by rw [← (hXW.zpow_right (-a)).eq]; group
          _ = 1 := by rw [hXX, (Commute.refl W).mul_zpow]; group
      have hvj : X * W ^ (-a) * j = j * (X * W ^ (-a)) := by
        have h1 : j * (X * W ^ (-a)) * j⁻¹ = (X * W ^ (-a))⁻¹ := by
          rw [show j * (X * W ^ (-a)) * j⁻¹ = (j * X * j⁻¹) * (j * W ^ (-a) * j⁻¹) by group,
            hjX, ← conj_zpow, hjW, inv_zpow', neg_neg, mul_inv_rev X (W ^ (-a)), ← zpow_neg,
            neg_neg]
          exact (hXW.inv_left.zpow_right a).eq
        rw [inv_eq_of_mul_eq_one_right hvv] at h1
        calc X * W ^ (-a) * j = j * (X * W ^ (-a)) * j⁻¹ * j := by rw [h1]
          _ = j * (X * W ^ (-a)) := by group
      rcases hΩ _ hvw hvj hvv with h | h
      · refine ⟨a, ?_⟩
        calc X = X * W ^ (-a) * W ^ a := by group
          _ = W ^ a := by rw [h, one_mul]
      · refine ⟨2 ^ (d + 1) + a, ?_⟩
        calc X = X * W ^ (-a) * W ^ a := by group
          _ = ρ * W ^ a := by rw [h]
          _ = W ^ ((2 ^ (d + 1) : ℕ) : ℤ) * W ^ a := by rw [zpow_natCast, hρW]
          _ = W ^ (2 ^ (d + 1) + a) := by rw [← zpow_add, Nat.cast_pow, Nat.cast_ofNat]
  obtain ⟨a, ha⟩ := key (m - 2) 1 le_rfl (by omega)
  exact ⟨a, by rw [pow_one] at ha; exact ha⟩

theorem false_of_conj_eq_inv_mul {j j₁ w w' ρ : P} {m : ℕ} {s : ℤ} (hm : 3 ≤ m)
    (hj : j * j = 1) (hj₁ : j₁ * j₁ = 1) (hw : orderOf w = 2 ^ m)
    (hρ : w ^ (2 ^ (m - 1)) = ρ) (hρ' : w' ^ (2 ^ (m - 1)) = ρ) (hρc : ∀ x : P, x * ρ = ρ * x)
    (hww' : w * w' = w' * w) (hjw : j * w * j⁻¹ = w⁻¹)
    (he : j₁ * w * j₁⁻¹ = w⁻¹ * ρ) (he' : j * w' * j⁻¹ = w'⁻¹ * ρ)
    (hs : j * j₁ * (j * j₁) = w ^ s)
    (hC : ∀ a b : P, a * j = j * a → b * j = j * b → a * b = b * a)
    (hinv' : ∀ v : P, v * j = j * v → v * v = 1 → v = 1 ∨ v = j ∨ v = ρ ∨ v = j * ρ) :
    False := by
  have hm1 : 1 ≤ m := by omega
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  have hj₁inv : j₁⁻¹ = j₁ := inv_eq_of_mul_eq_one_right hj₁
  obtain ⟨hρ2, hρ1⟩ := rho_mul_self_and_ne_one hm1 hw hρ
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hjρ : j * ρ * j⁻¹ = ρ := by rw [hρc j, mul_assoc, mul_inv_cancel, mul_one]
  have hρw : Commute ρ w := (hρc w).symm
  have hjwz : ∀ n : ℤ, j * w ^ n * j⁻¹ = w ^ (-n) := fun n => by
    rw [← conj_zpow, hjw, inv_zpow, zpow_neg]
  obtain ⟨t, hst⟩ : Even s := by
    have h1 := zpow_mul_conj_zpow_eq_one hj hj₁ hs
    rw [he, Commute.mul_zpow (hρc w⁻¹), inv_zpow', ← mul_assoc, ← zpow_add, add_neg_cancel,
      zpow_zero, one_mul] at h1
    rcases Int.even_or_odd s with hse | hso
    · exact hse
    · exact absurd (((zpow_eq_of_mul_self hρ2 s).2 hso).symm.trans h1) hρ1
  have hrw : j * j₁ * w * (j * j₁)⁻¹ = w * ρ := by
    rw [show j * j₁ * w * (j * j₁)⁻¹ = j * (j₁ * w * j₁⁻¹) * j⁻¹ by group, he,
      show j * (w⁻¹ * ρ) * j⁻¹ = (j * w * j⁻¹)⁻¹ * (j * ρ * j⁻¹) by group, hjw, hjρ, inv_inv]
  have hjr : j * (j * j₁) * j⁻¹ = (j * j₁)⁻¹ := by
    rw [mul_inv_rev, hjinv, hj₁inv]
    calc j * (j * j₁) * j = (j * j) * j₁ * j := by group
      _ = j₁ * j := by rw [hj, one_mul]
  set r := j * j₁ with hr
  have hrr : r * r = w ^ (t + t) := by rw [hs, hst]
  have hrinv : r⁻¹ = w ^ (-(t + t)) * r := by
    rw [zpow_neg, ← hrr]
    group
  have hyj : w ^ (-t) * r * j = j * (w ^ (-t) * r) := by
    have h1 : j * (w ^ (-t) * r) * j⁻¹ = w ^ (-t) * r := by
      rw [show j * (w ^ (-t) * r) * j⁻¹ = (j * w ^ (-t) * j⁻¹) * (j * r * j⁻¹) by group, hjwz,
        neg_neg, hjr, hrinv, ← mul_assoc, ← zpow_add, show t + -(t + t) = -t by ring]
    calc w ^ (-t) * r * j = j * (w ^ (-t) * r) * j⁻¹ * j := by rw [h1]
      _ = j * (w ^ (-t) * r) := by group
  have hyy : w ^ (-t) * r * (w ^ (-t) * r) = ρ ^ (-t) := by
    have hrwz : r * w ^ (-t) * r⁻¹ = (w * ρ) ^ (-t) := by rw [← conj_zpow, hrw]
    calc w ^ (-t) * r * (w ^ (-t) * r) = w ^ (-t) * (r * w ^ (-t) * r⁻¹) * (r * r) := by group
      _ = w ^ (-t) * w ^ (-t) * (ρ ^ (-t) * w ^ (t + t)) := by
          rw [hrwz, hrr, Commute.mul_zpow (hρc w)]; group
      _ = w ^ (-t) * w ^ (-t) * (w ^ (t + t) * ρ ^ (-t)) := by
          rw [((hρw.zpow_left (-t)).zpow_right (t + t)).eq]
      _ = ρ ^ (-t) := by group
  have hyy' : w ^ (-t) * r * (w ^ (-t) * r) = 1 ∨ w ^ (-t) * r * (w ^ (-t) * r) = ρ := by
    rw [hyy]
    rcases Int.even_or_odd (-t) with h | h
    · exact Or.inl ((zpow_eq_of_mul_self hρ2 _).1 h)
    · exact Or.inr ((zpow_eq_of_mul_self hρ2 _).2 h)
  have hyw : w ^ (-t) * r * w * (w ^ (-t) * r)⁻¹ = w * ρ := by
    calc w ^ (-t) * r * w * (w ^ (-t) * r)⁻¹ = w ^ (-t) * (r * w * r⁻¹) * w ^ t := by group
      _ = w ^ (-t) * w * (ρ * w ^ t) := by rw [hrw]; group
      _ = w ^ (-t) * w * (w ^ t * ρ) := by rw [← hρc (w ^ t)]
      _ = w * ρ := by group
  obtain ⟨a, ha⟩ := exists_pow_two_eq_zpow (by omega) hw hρ hρ' hρc hww' hjw he' hinv'
  have hwa : w ^ a * w ^ a = w' * w' := by
    rw [← (Commute.refl w).mul_zpow, ← pow_two, ← ha, pow_two]
  have hw'w : Commute w' w := Commute.symm hww'
  set u := w' * w ^ (-a) with hu
  have huw : Commute u w := hw'w.mul_left ((Commute.refl w).zpow_left (-a))
  have hju : j * u * j⁻¹ = u * ρ := by
    calc j * u * j⁻¹ = (j * w' * j⁻¹) * (j * w ^ (-a) * j⁻¹) := by rw [hu]; group
      _ = w'⁻¹ * (ρ * w ^ a) := by rw [he', hjwz, neg_neg]; group
      _ = w'⁻¹ * (w ^ a * ρ) := by rw [← hρc (w ^ a)]
      _ = w'⁻¹ * (w ^ a * w ^ a) * w ^ (-a) * ρ := by group
      _ = w'⁻¹ * (w' * w') * w ^ (-a) * ρ := by rw [hwa]
      _ = u * ρ := by rw [hu]; group
  have huu : u * u = 1 := by
    calc u * u = w' * (w ^ (-a) * w') * w ^ (-a) := by rw [hu]; group
      _ = w' * w' * (w ^ (-a) * w ^ (-a)) := by
          rw [← (hw'w.zpow_right (-a)).eq]; group
      _ = 1 := by rw [← hwa]; group
  set q := w ^ (2 ^ (m - 2)) with hq
  have hqq : q * q = ρ := by
    rw [hq, ← pow_add, ← two_mul, ← pow_succ', show m - 2 + 1 = m - 1 by omega, hρ]
  have hjq : j * q * j⁻¹ = q⁻¹ := by rw [hq, ← conj_pow, hjw, inv_pow]
  have hqinv := inv_eq_mul_of_mul_self_eq hqq hρ2
  have hqw : Commute q w := (Commute.refl w).pow_left _
  have hqu : Commute q u := Commute.symm (Commute.pow_right huw _)
  have hcw : Commute (q * u) w := hqw.mul_left huw
  have hcj : q * u * j = j * (q * u) := by
    have h1 : j * (q * u) * j⁻¹ = q * u := by
      rw [show j * (q * u) * j⁻¹ = (j * q * j⁻¹) * (j * u * j⁻¹) by group, hjq, hju, hqinv,
        mul_assoc q ρ, ← mul_assoc ρ u ρ, ← hρc u, mul_assoc u ρ ρ, hρ2, mul_one]
    calc q * u * j = j * (q * u) * j⁻¹ * j := by rw [h1]
      _ = j * (q * u) := by group
  have hcc : q * u * (q * u) = ρ := by
    calc q * u * (q * u) = q * (u * q) * u := by group
      _ = q * q * (u * u) := by rw [← hqu.eq]; group
      _ = ρ := by rw [hqq, huu, mul_one]
  have hinvw : ∀ x : P, Commute x w → x * j * w * (x * j)⁻¹ = w⁻¹ := fun x hx => by
    calc x * j * w * (x * j)⁻¹ = x * (j * w * j⁻¹) * x⁻¹ := by group
      _ = w⁻¹ := by rw [hjw, (hx.inv_right).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hfinal : Commute (w ^ (-t) * r) w ∨
      w ^ (-t) * r * w * (w ^ (-t) * r)⁻¹ = w⁻¹ := by
    rcases hyy' with h | h
    · rcases hinv' _ hyj h with h' | h' | h' | h' <;> rw [h']
      · exact Or.inl (Commute.one_left w)
      · exact Or.inr hjw
      · exact Or.inl hρw
      · right
        rw [hρc j]
        exact hinvw ρ hρw
    · rcases eq_mul_of_mul_self_eq hC hinv' hyj hcj (by rw [h, hcc]) with h' | h' | h' | h' <;>
        rw [h']
      · exact Or.inl hcw
      · exact Or.inr (hinvw _ hcw)
      · exact Or.inl (hcw.mul_left hρw)
      · right
        rw [hρc j, ← mul_assoc]
        exact hinvw _ (hcw.mul_left hρw)
  rcases hfinal with h | h
  · apply hρ1
    have h1 : w * ρ = w := by rw [← hyw, h.eq, mul_assoc, mul_inv_cancel, mul_one]
    calc ρ = w⁻¹ * (w * ρ) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]
  · have h5 : w * w = ρ := by
      have h6 : w * ρ = w⁻¹ := hyw.symm.trans h
      calc w * w = w * (w * ρ) * ρ⁻¹ := by group
        _ = ρ := by rw [h6, mul_inv_cancel, one_mul, hρinv]
    have h4 : w ^ 4 = 1 := by rw [show 4 = 2 + 2 by norm_num, pow_add, pow_two, h5, hρ2]
    have := le_two_of_pow_four hw h4
    omega

end GMS43

end CFSG.SeitzReduction.RankOne
