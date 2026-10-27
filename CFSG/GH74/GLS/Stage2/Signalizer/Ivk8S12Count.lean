module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

theorem factorization_two_eq {n k : ℕ} (hdvd : 2 ^ k ∣ n) (hnd : ¬ 2 ^ (k + 1) ∣ n) :
    n.factorization 2 = k := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hnd (dvd_zero _)
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).1 hdvd
  have h2 : ¬ k + 1 ≤ n.factorization 2 := fun h =>
    hnd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).2 h)
  omega

theorem normal_of_normalized_three {C : Type*} [Group C] [Finite C] (hcard : Nat.card C = 1920)
    {T E : Subgroup C} (hT : Nat.card T = 128) (hE3 : IsPGroup 3 ↥E) (hEne : E ≠ ⊥)
    (hN : T ≤ normalizer (E : Set C)) : E.Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card C).factorization 3 = 1 := by
    rw [hcard]
    have hpos : (1920 : ℕ) ≠ 0 := by norm_num
    have h1 : 1 ≤ (1920 : ℕ).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).1 (by norm_num)
    have h2 : ¬ 2 ≤ (1920 : ℕ).factorization 3 := fun h =>
      absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).2 h) (by norm_num)
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
  have hk1 : k = 1 := by
    have hdvd : 3 ^ k ∣ 1920 := by
      rw [← hcard, ← hk]
      exact Subgroup.card_subgroup_dvd_card E
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hEne (Subgroup.card_eq_one.1 (by simpa using hk))
    have hk2 : ¬ 2 ≤ k := fun h =>
      absurd ((Nat.pow_dvd_pow 3 h).trans hdvd) (by norm_num)
    omega
  have hEcard : Nat.card E = 3 ^ (Nat.card C).factorization 3 := by
    rw [hk, hk1, hfac]
  let P : Sylow 3 C := Sylow.ofCard E hEcard
  have hP : (P : Subgroup C) = E := Sylow.coe_ofCard E hEcard
  have hmod := card_sylow_modEq_one 3 C
  have hidx := Sylow.card_eq_index_normalizer P
  have hPset : (P : Set C) = (E : Set C) := congrArg (fun K : Subgroup C => (K : Set C)) hP
  rw [hPset] at hidx
  have hTindex : T.index = 15 := by
    have h := T.card_mul_index
    rw [hT, hcard] at h
    omega
  have h1 := Subgroup.index_dvd_of_le hN
  rw [hTindex] at h1
  rw [hidx] at hmod
  have hle : (normalizer (E : Set C)).index ≤ 15 := Nat.le_of_dvd (by norm_num) h1
  have hone : (normalizer (E : Set C)).index = 1 := by
    generalize (normalizer (E : Set C)).index = m at h1 hmod hle
    have : m % 3 = 1 := hmod
    interval_cases m <;> simp_all
  have htop : normalizer (E : Set C) = ⊤ := Subgroup.index_eq_one.1 hone
  exact Subgroup.normalizer_eq_top_iff.1 htop

theorem not_three_of_odd_trivial {X : Type*} [Group X] [Finite X] {C T E : Subgroup X}
    (hcard : Nat.card C = 1920) (hodd : ∀ N : Subgroup C, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hTC : T ≤ C) (hT : Nat.card T = 128) (hEC : E ≤ C) (hE3 : IsPGroup 3 ↥E) (hEne : E ≠ ⊥)
    (hN : T ≤ normalizer (E : Set X)) : False := by
  have hT' : Nat.card (T.subgroupOf C) = 128 := by
    rw [← hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv
  have hE3' : IsPGroup 3 ↥(E.subgroupOf C) :=
    hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hEC).symm
  have hEne' : E.subgroupOf C ≠ ⊥ := by
    intro h
    apply hEne
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ C := hEC hx
    have : (⟨x, hxC⟩ : C) ∈ E.subgroupOf C := hx
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hN' : T.subgroupOf C ≤ normalizer ((E.subgroupOf C : Subgroup C) : Set C) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have := Subgroup.mem_normalizer_iff.mp (hN ht) (z : X)
    exact this
  have hnorm := normal_of_normalized_three hcard hT' hE3' hEne' hN'
  have hodd' : Odd (Nat.card (E.subgroupOf C)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3'
    rw [hk]
    exact Odd.pow (by decide)
  exact hEne' (hodd _ hnorm hodd')

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
