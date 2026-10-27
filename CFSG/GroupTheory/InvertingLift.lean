module

public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Vol2.Ch4Sec4Frattini
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Arith

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_inverting_of_inverting_mod {P A : Subgroup G} {t₀ : G}
    (hP2 : IsPGroup 2 P) (hAP : A ≤ normalizer (P : Set G)) (hAodd : Odd (Nat.card A))
    (ht₀P : t₀ ∈ normalizer (P : Set G)) (ht₀2 : ∃ k : ℕ, orderOf t₀ = 2 ^ k)
    (hinv : ∀ a ∈ A, t₀ * a * t₀⁻¹ * a ∈ P) :
    ∃ y ∈ P, (∃ k : ℕ, orderOf (y * t₀) = 2 ^ k) ∧
      ∀ a ∈ A, (y * t₀) * a * (y * t₀)⁻¹ = a⁻¹ := by
  have hmB : A.map (MulAut.conj t₀).toMonoidHom ≤ A ⊔ P := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem : t₀ * a * t₀⁻¹ * a ∈ P := hinv a ha
    have he : t₀ * a * t₀⁻¹ = (t₀ * a * t₀⁻¹ * a) * a⁻¹ := by group
    show t₀ * a * t₀⁻¹ ∈ A ⊔ P
    have h2 : (t₀ * a * t₀⁻¹ * a) * a⁻¹ ∈ P ⊔ A :=
      Subgroup.mul_mem_sup hmem (A.inv_mem ha)
    rw [he]
    rwa [sup_comm]
  obtain ⟨y, hyP, hyN⟩ :=
    CFSG.Quasithin.H13.exists_mul_mem_normalizer hP2 hAodd hAP ht₀P hmB
  have hAPbot : A ⊓ P = ⊥ := by
    rw [inf_comm]
    exact CFSG.Quasithin.H13.inf_eq_bot_of_isPGroup_two_of_odd hP2 hAodd
  refine ⟨y, hyP, ?_, ?_⟩
  ·
    have ht0g : IsPGroup 2 (Subgroup.zpowers t₀) := by
      obtain ⟨k, hk⟩ := ht₀2
      have hcard : Nat.card (Subgroup.zpowers t₀) = 2 ^ k := by
        rw [Nat.card_zpowers, hk]
      exact IsPGroup.of_card hcard
    have hsup : IsPGroup 2 (P ⊔ Subgroup.zpowers t₀ : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hP2 ht0g (Subgroup.zpowers_le.mpr ht₀P)
    obtain ⟨k, hk⟩ := hsup.exists_orderOf_eq_pow
      ⟨y * t₀, Subgroup.mul_mem_sup hyP (Subgroup.mem_zpowers t₀)⟩
    exact ⟨k, (Subgroup.orderOf_coe _).trans hk⟩
  · intro a ha
    have hbA : (y * t₀) * a * (y * t₀)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hyN a).mp ha
    have hq' : a⁻¹ * y⁻¹ * a ∈ P := by
      have h := (Subgroup.mem_normalizer_iff.mp (hAP (A.inv_mem ha)) y).mp hyP
      simpa [mul_assoc] using P.inv_mem h
    have hbP : ((y * t₀) * a * (y * t₀)⁻¹) * a ∈ P := by
      have he : ((y * t₀) * a * (y * t₀)⁻¹) * a =
          y * (t₀ * a * t₀⁻¹ * a) * (a⁻¹ * y⁻¹ * a) := by group
      rw [he]
      exact P.mul_mem (P.mul_mem hyP (hinv a ha)) hq'
    have hmem : ((y * t₀) * a * (y * t₀)⁻¹) * a ∈ A ⊓ P := ⟨A.mul_mem hbA ha, hbP⟩
    rw [hAPbot] at hmem
    have h1 : ((y * t₀) * a * (y * t₀)⁻¹) * a = 1 := Subgroup.mem_bot.mp hmem
    calc (y * t₀) * a * (y * t₀)⁻¹
        = (((y * t₀) * a * (y * t₀)⁻¹) * a) * a⁻¹ := by group
      _ = a⁻¹ := by rw [h1, one_mul]

theorem exists_prime_choice {n : ℕ} (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ n - 1 ∧ r ≠ 5 ∧ (3 ∣ 2 ^ n - 1 → r = 3) := by
  by_cases h3 : 3 ∣ 2 ^ n - 1
  · exact ⟨3, Nat.prime_three, h3, by norm_num, fun _ => rfl⟩
  ·
    have hodd : Odd n := by
      rw [← Nat.not_even_iff_odd]
      intro hn
      apply h3
      have hmod : 2 ^ n % 3 = 1 := CFSG.two_pow_mod_three_of_even hn
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      apply (Nat.modEq_iff_dvd' hpos).mp
      change 1 % 3 = 2 ^ n % 3
      norm_num [hmod]
    have h5 : ¬ 5 ∣ 2 ^ n - 1 := by
      obtain ⟨m, rfl⟩ := hodd
      exact CFSG.SignalizerFunctorTheorem.McBride.SzModel.not_five_dvd_two_pow_sub_one m
    have hne : 2 ^ n - 1 ≠ 1 := by
      have h8 : 8 ≤ 2 ^ n := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd hne
    exact ⟨r, hrp, hrdvd, fun h => h5 (h ▸ hrdvd), fun h => absurd h h3⟩

end CFSG.GroupTheory
