module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbedding

theorem modEq_one_of_pow_three_modEq_one {k m : ℕ} (h : m ^ 3 ≡ 1 [MOD 3 ^ k]) :
    m ≡ 1 [MOD 3 ^ (k - 1)] := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> exact Nat.modEq_one
  have h3 : m ^ 3 ≡ 1 [MOD 3] := h.of_dvd (dvd_pow_self 3 (by omega))
  have hm : m % 3 = 1 := by
    have hlt : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hpow := Nat.pow_mod m 3 3
    unfold Nat.ModEq at h3
    interval_cases hr : m % 3 <;> simp_all
  obtain ⟨t, rfl⟩ : ∃ t, m = 3 * t + 1 := ⟨m / 3, by omega⟩
  have hexp : (3 * t + 1) ^ 3 = 9 * t * (3 * (t ^ 2 + t) + 1) + 1 := by ring
  rw [hexp] at h
  have hdvd : 3 ^ k ∣ 9 * t * (3 * (t ^ 2 + t) + 1) := by
    have := (Nat.modEq_iff_dvd' (by omega)).mp h.symm
    simpa using this
  have hcop : Nat.Coprime (3 ^ k) (3 * (t ^ 2 + t) + 1) := by
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
    omega
  have h9 : 3 ^ k ∣ 9 * t := hcop.dvd_of_dvd_mul_right hdvd
  have hk' : 3 ^ k = 9 * 3 ^ (k - 2) := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [hk'] at h9
  have ht : 3 ^ (k - 2) ∣ t := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9
  refine ((Nat.modEq_iff_dvd' (by omega)).mpr ?_).symm
  rw [show 3 * t + 1 - 1 = 3 * t by omega, show k - 1 = (k - 2) + 1 by omega, pow_succ,
    mul_comm _ 3]
  exact Nat.mul_dvd_mul_left 3 ht

theorem mul_modEq_of_pow_three {k m j : ℕ} (hk : 3 ≤ k) (h : m ^ 3 ≡ 1 [MOD 3 ^ k])
    (hj : 3 ^ (k - 2) ∣ j) : m * j ≡ j [MOD 3 ^ k] := by
  obtain ⟨i, rfl⟩ := hj
  have h1 := (modEq_one_of_pow_three_modEq_one h).mul_right' (3 ^ (k - 2))
  have hdvd : 3 ^ k ∣ 3 ^ (k - 1) * 3 ^ (k - 2) := by
    rw [← pow_add]
    exact pow_dvd_pow 3 (by omega)
  have h2 := (h1.mul_right i).of_dvd hdvd
  simpa [mul_assoc] using h2

variable {X : Type*} [Group X] [Finite X]

theorem conj_eq_of_mem_normalizer_isCyclic {C : Subgroup X} (hC : IsCyclic C)
    (hC3 : IsPGroup 3 C) (h27 : 27 ≤ Nat.card C) {a : X}
    (ha : a ∈ Subgroup.normalizer (C : Set X)) (ha3 : a ^ 3 = 1) {g : X} (hg : g ∈ C)
    (hg9 : g ^ 9 = 1) : a * g * a⁻¹ = g := by
  obtain ⟨⟨h, hhC⟩, hgen⟩ := hC.exists_generator
  obtain ⟨k, hk⟩ := hC3.exists_card_eq
  have hord : orderOf h = 3 ^ k := by
    rw [← hk, ← orderOf_eq_card_of_forall_mem_zpowers hgen, Subgroup.orderOf_mk]
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpow : ∀ x ∈ C, ∃ n : ℕ, h ^ n = x := by
    intro x hx
    obtain ⟨n, hn⟩ := (hgen ⟨x, hx⟩)
    have hfin : (⟨x, hx⟩ : C) ∈ Submonoid.powers (⟨h, hhC⟩ : C) :=
      mem_powers_iff_mem_zpowers.mpr ⟨n, hn⟩
    obtain ⟨m, hm⟩ := hfin
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  obtain ⟨m, hm⟩ := hpow _ ((Subgroup.mem_normalizer_iff.mp ha h).mp hhC)
  have hconj : ∀ n : ℕ, a * h ^ n * a⁻¹ = h ^ (m * n) := by
    intro n
    rw [pow_mul, hm, conj_pow]
  have hcube : h ^ (m ^ 3) = h ^ 1 := by
    have ha3' : a * (a * a) = 1 := by rw [← ha3, pow_three]
    have e1 : a * (a * (a * h * a⁻¹) * a⁻¹) * a⁻¹ = h := by
      have e : a * (a * (a * h * a⁻¹) * a⁻¹) * a⁻¹ = (a * (a * a)) * h * (a * (a * a))⁻¹ := by
        group
      rw [e, ha3', one_mul, inv_one, mul_one]
    have e2 : a * (a * (a * h * a⁻¹) * a⁻¹) * a⁻¹ = h ^ (m * (m * m)) := by
      rw [show a * h * a⁻¹ = h ^ m from hm.symm, hconj m, hconj (m * m)]
    have hm3 : m ^ 3 = m * (m * m) := by ring
    rw [hm3, ← e2, e1, pow_one]
  have hmod : m ^ 3 ≡ 1 [MOD 3 ^ k] := hord ▸ (pow_eq_pow_iff_modEq.mp hcube)
  obtain ⟨j, rfl⟩ := hpow g hg
  have hj : 3 ^ (k - 2) ∣ j := by
    have h9 : orderOf h ∣ 9 * j := orderOf_dvd_of_pow_eq_one (by rw [mul_comm, pow_mul, hg9])
    rw [hord, show (9 : ℕ) = 3 ^ 2 by norm_num, show k = 2 + (k - 2) by omega, pow_add] at h9
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9
  rw [hconj, pow_eq_pow_iff_modEq, hord]
  exact mul_modEq_of_pow_three hk3 hmod hj

theorem exists_orderOf_eq_nine_of_isCyclic {S : Subgroup X} (hS : IsCyclic S) (hS3 : IsPGroup 3 S)
    (h9 : 9 ≤ Nat.card S) : ∃ g ∈ S, orderOf g = 9 := by
  obtain ⟨k, hk⟩ := hS3.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨⟨h, hhS⟩, hgen⟩ := hS.exists_generator
  have hord : orderOf h = 3 ^ k := by
    rw [← hk, ← orderOf_eq_card_of_forall_mem_zpowers hgen, Subgroup.orderOf_mk]
  refine ⟨h ^ (3 ^ (k - 2)), S.pow_mem hhS _, ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (hord ▸ pow_dvd_pow 3 (by omega)), hord,
    Nat.pow_div (by omega) (by norm_num), show k - (k - 2) = 2 by omega]

end CFSG.AGLEmbedding
