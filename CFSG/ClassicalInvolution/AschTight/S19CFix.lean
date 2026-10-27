module

public import CFSG.ClassicalInvolution.AschTight.Sec7L714A

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G]

theorem conj_comm_eq_inv {a s : G} (ha2 : a * a = 1) :
    a * (a * s * a⁻¹ * s⁻¹) * a⁻¹ = (a * s * a⁻¹ * s⁻¹)⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  calc a * (a * s * a⁻¹ * s⁻¹) * a⁻¹ = (a * a) * s * a⁻¹ * s⁻¹ * a⁻¹ := by group
    _ = s * a⁻¹ * s⁻¹ * a⁻¹ := by rw [ha2, one_mul]
    _ = s * a * s⁻¹ * a⁻¹ := by rw [show s * a⁻¹ = s * a by rw [hai]]
    _ = (a * s * a⁻¹ * s⁻¹)⁻¹ := by group

theorem mul_self_eq_one_of_zpow {u y : G} {k : ℕ} (hk : 2 ≤ k) (hu : orderOf u = 2 ^ (k + 1))
    (hy : y ∈ Subgroup.zpowers u) (hy1 : y ^ ((2 : ℤ) ^ k + 2) = 1) : y * y = 1 := by
  have hdvd : orderOf y ∣ 2 ^ (k + 1) := hu ▸ orderOf_dvd_of_mem_zpowers hy
  obtain ⟨j, -, hjy⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hd2 : ((orderOf y : ℕ) : ℤ) ∣ (2 : ℤ) ^ k + 2 := orderOf_dvd_iff_zpow_eq_one.mpr hy1
  have hj1 : j ≤ 1 := by
    by_contra hj1
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    rw [hjy] at hd2
    push_cast at hd2
    have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ (k' + 2) + 2 :=
      dvd_trans ⟨2 ^ j', by ring⟩ hd2
    have h4' : (4 : ℤ) ∣ (2 : ℤ) ^ (k' + 2) := ⟨2 ^ k', by ring⟩
    have h42 : (4 : ℤ) ∣ 2 := by simpa using dvd_sub h4 h4'
    norm_num at h42
  rw [← sq]
  exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hjy]; exact pow_dvd_pow 2 hj1)

theorem exists_mul_fixed {u s a : G} {k : ℕ} (hk : 2 ≤ k) (hu : orderOf u = 2 ^ (k + 1))
    (ha2 : a * a = 1) (has : a * s * a⁻¹ * s⁻¹ ∈ Subgroup.zpowers u)
    (hact : (∀ x ∈ Subgroup.zpowers u, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∨
      ∀ x ∈ Subgroup.zpowers u, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k - 1)) :
    ∃ w ∈ Subgroup.zpowers u, a * (w * s) * a⁻¹ = w * s := by
  set y := a * s * a⁻¹ * s⁻¹ with hy
  have hay : a * y * a⁻¹ = y⁻¹ := conj_comm_eq_inv ha2
  have hconj : ∀ w : G, a * (w * s) * a⁻¹ = (a * w * a⁻¹) * (y * s) := by
    intro w
    rw [hy]
    group
  have hu2 : u ^ ((2 : ℤ) ^ (k + 1)) = 1 := by
    rw [show ((2 : ℤ) ^ (k + 1)) = ((2 ^ (k + 1) : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← hu,
      pow_orderOf_eq_one]
  rcases hact with h1 | h2
  · have hy1 : y ^ ((2 : ℤ) ^ k + 2) = 1 := by
      have := h1 y has
      rw [hay] at this
      rw [show (2 : ℤ) ^ k + 2 = ((2 : ℤ) ^ k + 1) + 1 by ring, zpow_add, ← this, zpow_one,
        inv_mul_cancel]
    have hyy := mul_self_eq_one_of_zpow hk hu has hy1
    rcases (Sec7.isUniqueInvolution_zpowers hu).unique y has hyy with hy1' | hyz
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [hconj, hy1']
      simp
    · refine ⟨u, Subgroup.mem_zpowers u, ?_⟩
      rw [hconj, h1 u (Subgroup.mem_zpowers u), hyz, ← zpow_natCast u (2 ^ k), ← mul_assoc,
        ← zpow_add]
      push_cast
      rw [show (2 : ℤ) ^ k + 1 + 2 ^ k = 2 ^ (k + 1) + 1 by ring, zpow_add, hu2, one_mul, zpow_one]
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp has
    have hyk : y ^ ((2 : ℤ) ^ k) = 1 := by
      have := h2 y has
      rw [hay] at this
      rw [show (2 : ℤ) ^ k = ((2 : ℤ) ^ k - 1) + 1 by ring, zpow_add, ← this, zpow_one,
        inv_mul_cancel]
    have hev : (2 : ℤ) ∣ m := by
      rw [← hm, ← zpow_mul] at hyk
      have hd := orderOf_dvd_iff_zpow_eq_one.mpr hyk
      rw [hu] at hd
      push_cast at hd
      rw [show (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k by ring] at hd
      exact (mul_dvd_mul_iff_right (by positivity : (2 : ℤ) ^ k ≠ 0)).mp hd
    obtain ⟨b, rfl⟩ := hev
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have hc : Odd ((2 : ℤ) ^ (k' + 1) - 1) := ⟨2 ^ k' - 1, by ring⟩
    have hmem : u ^ (-b) ∈ Subgroup.zpowers (u ^ ((2 : ℤ) ^ (k' + 1) - 1)) := by
      rw [Sec71.zpowers_zpow_eq_of_odd hu hc]
      exact zpow_mem (Subgroup.mem_zpowers u) _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← zpow_mul] at hj
    refine ⟨u ^ j, zpow_mem (Subgroup.mem_zpowers u) _, ?_⟩
    rw [hconj, h2 _ (zpow_mem (Subgroup.mem_zpowers u) _), ← hm, ← mul_assoc, ← zpow_mul,
      ← zpow_add]
    congr 1
    have e1 : j * ((2 : ℤ) ^ (k' + 2) - 1) + 2 * b =
        j + (((2 : ℤ) ^ (k' + 1) - 1) * j * 2 + b * 2) := by ring
    rw [e1, zpow_add, zpow_add, zpow_mul, hj, ← zpow_mul, ← zpow_add]
    simp

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
