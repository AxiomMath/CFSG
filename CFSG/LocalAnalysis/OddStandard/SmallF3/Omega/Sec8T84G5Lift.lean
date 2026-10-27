module

public import CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset

section Helpers

variable {G : Type*} [Group G]

theorem sec8t84g5_fixed_coset [Finite G] {p : ℕ} [Fact p.Prime] {A O : Subgroup G}
    (hA : IsPGroup p A) (hAO : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O) (hp : ¬ p ∣ Nat.card O)
    {m : G} (hm : ∀ a ∈ A, a * m * a⁻¹ * m⁻¹ ∈ O) :
    ∃ c : G, c * m⁻¹ ∈ O ∧ ∀ a ∈ A, a * c * a⁻¹ = c := by
  let ρ : ↥A →* MulAut G := MulAut.conj.comp A.subtype
  have hρ : ∀ (b : ↥A) (x : G), ρ b x = (b : G) * x * (b : G)⁻¹ := fun b x => rfl
  have hR : ∀ b : ↥A, ∀ r ∈ O, ρ b r ∈ O := fun b r hr => by
    rw [hρ]; exact hAO b b.2 r hr
  have hx : ∀ b : ↥A, ρ b m * m⁻¹ ∈ O := fun b => by
    rw [hρ]; exact hm b b.2
  letI : MulAction ↥A (Coset O m) := cosetAction ρ O hR m hx
  obtain ⟨y, hy⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Coset O m)
    (by rw [natCard_coset]; exact hp)
  refine ⟨y.1, y.2, fun a ha => ?_⟩
  exact congrArg Subtype.val (hy ⟨a, ha⟩)

theorem sec8t84g5_pow_cong {Q O : Subgroup G} (hOn : ∀ q ∈ Q, ∀ o ∈ O, q * o * q⁻¹ ∈ O)
    {x y : G} (hy : y ∈ Q) (hxy : x * y⁻¹ ∈ O) (n : ℕ) : x ^ n * (y ^ n)⁻¹ ∈ O := by
  induction n with
  | zero => simp [O.one_mem]
  | succ n ih =>
    have h := O.mul_mem ih (hOn (y ^ n) (Q.pow_mem hy n) _ hxy)
    have e : x ^ (n + 1) * (y ^ (n + 1))⁻¹ =
        x ^ n * (y ^ n)⁻¹ * (y ^ n * (x * y⁻¹) * (y ^ n)⁻¹) := by
      rw [pow_succ, pow_succ]; group
    rw [e]; exact h

end Helpers

theorem sec8t84g5_lift {G : Type} [Group G] [Finite G] {O : Subgroup G} {γ m : G}
    (hOodd : Odd (Nat.card O)) (hmO : m ∈ normalizer (O : Set G))
    (hγO : γ ∈ normalizer (O : Set G)) (hγ2 : γ * γ = 1)
    (hm3 : ∃ k : ℕ, m ^ (3 ^ k) ∈ O) (hγm : γ * m * γ⁻¹ * m⁻¹ ∈ O) :
    ∃ y : G, y ∈ zpowers m ⊔ O ∧ m⁻¹ * y ∈ O ∧ γ * y * γ⁻¹ = y ∧ ∃ k : ℕ, orderOf y = 3 ^ k := by
  have hHn : zpowers m ⊔ O ≤ normalizer (O : Set G) :=
    sup_le (zpowers_le.mpr hmO) Subgroup.le_normalizer
  have hOn : ∀ q ∈ zpowers m ⊔ O, ∀ o ∈ O, q * o * q⁻¹ ∈ O :=
    fun q hq o ho => (Subgroup.mem_normalizer_iff.mp (hHn hq) o).mp ho
  have hγO' : ∀ o ∈ O, γ * o * γ⁻¹ ∈ O :=
    fun o ho => (Subgroup.mem_normalizer_iff.mp hγO o).mp ho
  have hp2 : ¬ 2 ∣ Nat.card O := by
    rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := hOodd
    omega
  have hγ1 : γ ^ 2 = 1 := by rw [pow_two]; exact hγ2
  have hA : IsPGroup 2 (zpowers γ) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hγ1) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have hz2 : γ ^ (2 : ℤ) = 1 := by exact_mod_cast hγ1
  have hmem : ∀ a ∈ zpowers γ, a = 1 ∨ a = γ := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have key : γ ^ n = γ ^ (n % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
      rw [zpow_add, zpow_mul, hz2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left; rw [key, h]; exact zpow_zero γ
    · right; rw [key, h]; exact zpow_one γ
  obtain ⟨c, hc, hcA⟩ := sec8t84g5_fixed_coset (p := 2) hA
    (fun a ha o ho => by
      rcases hmem a ha with rfl | rfl
      · simpa using ho
      · exact hγO' o ho)
    hp2
    (fun a ha => by
      rcases hmem a ha with rfl | rfl
      · simp [O.one_mem]
      · exact hγm)
  have hmH : m ∈ zpowers m ⊔ O := Subgroup.mem_sup_left (mem_zpowers m)
  have hcH : c ∈ zpowers m ⊔ O := by
    have e : c = (c * m⁻¹) * m := by group
    rw [e]; exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) hmH
  obtain ⟨k0, hk0⟩ := hm3
  have hmκ : m ^ 3 ^ (k0 + 1) ∈ O := by
    rw [pow_succ, pow_mul]; exact O.pow_mem hk0 3
  have hcκ : c ^ 3 ^ (k0 + 1) ∈ O := by
    have h := sec8t84g5_pow_cong hOn hmH hc (3 ^ (k0 + 1))
    have e : c ^ 3 ^ (k0 + 1) =
        (c ^ 3 ^ (k0 + 1) * (m ^ 3 ^ (k0 + 1))⁻¹) * m ^ 3 ^ (k0 + 1) := by group
    rw [e]; exact O.mul_mem h hmκ
  have hcd : c ^ (3 ^ (k0 + 1) * Nat.card O) = 1 := by
    rw [pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard O hcκ)
  have hOpos : 0 < Nat.card O := Nat.card_pos
  obtain ⟨e, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (n := 3 ^ (k0 + 1) * Nat.card O) (by positivity) 3 (by norm_num)
  have hb3 : Nat.Coprime 3 b := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb
  have hcop : Nat.Coprime (3 ^ e) b := Nat.Coprime.pow_left e hb3
  have hκe : 3 ^ (k0 + 1) ∣ 3 ^ e :=
    (Nat.Coprime.pow_left (k0 + 1) hb3).dvd_of_dvd_mul_right (hab ▸ dvd_mul_right _ _)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 0
  have hbk : b ∣ k := Nat.modEq_zero_iff_dvd.mp hk2
  have hkκ : k % 3 ^ (k0 + 1) = 1 := by
    have h := Nat.ModEq.of_dvd hκe hk1
    have h1 : 1 < 3 ^ (k0 + 1) := Nat.one_lt_pow (by omega) (by norm_num)
    simpa [Nat.ModEq, Nat.mod_eq_of_lt h1] using h
  obtain ⟨j, rfl⟩ : ∃ j, k = 3 ^ (k0 + 1) * j + 1 :=
    ⟨k / 3 ^ (k0 + 1), by have := Nat.div_add_mod k (3 ^ (k0 + 1)); rw [hkκ] at this; omega⟩
  refine ⟨c ^ (3 ^ (k0 + 1) * j + 1), Subgroup.pow_mem _ hcH _, ?_, ?_, ?_⟩
  · have h1 := sec8t84g5_pow_cong hOn hmH hc (3 ^ (k0 + 1) * j + 1)
    have h2 : m ^ (3 ^ (k0 + 1) * j + 1) * m⁻¹ ∈ O := by
      have e2 : m ^ (3 ^ (k0 + 1) * j + 1) * m⁻¹ = (m ^ 3 ^ (k0 + 1)) ^ j := by
        rw [pow_succ, pow_mul]; group
      rw [e2]; exact O.pow_mem hmκ j
    have h3 : c ^ (3 ^ (k0 + 1) * j + 1) * m⁻¹ ∈ O := by
      have e3 : c ^ (3 ^ (k0 + 1) * j + 1) * m⁻¹ =
          (c ^ (3 ^ (k0 + 1) * j + 1) * (m ^ (3 ^ (k0 + 1) * j + 1))⁻¹) *
            (m ^ (3 ^ (k0 + 1) * j + 1) * m⁻¹) := by group
      rw [e3]; exact O.mul_mem h1 h2
    have e4 : m⁻¹ * c ^ (3 ^ (k0 + 1) * j + 1) =
        m⁻¹ * (c ^ (3 ^ (k0 + 1) * j + 1) * m⁻¹) * m := by group
    rw [e4]
    have h4 := (Subgroup.mem_normalizer_iff.mp (inv_mem hmO) _).mp h3
    rwa [inv_inv] at h4
  · rw [← conj_pow, hcA γ (mem_zpowers γ)]
  · have hy : (c ^ (3 ^ (k0 + 1) * j + 1)) ^ 3 ^ e = 1 := by
      rw [← pow_mul]
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      have h1 : orderOf c ∣ 3 ^ (k0 + 1) * Nat.card O := orderOf_dvd_of_pow_eq_one hcd
      rw [hab] at h1
      exact h1.trans (by rw [mul_comm (3 ^ (k0 + 1) * j + 1)]; exact mul_dvd_mul_left _ hbk)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy)
    exact ⟨i, hi⟩

end CFSG.OddStandard.SmallF3.Omega
