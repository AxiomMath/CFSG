module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.ComponentClassification.SolMax

open Subgroup

variable {X : Type} [Group X]

theorem exists_oddPart_of_card_le_two [Finite X] {K : Subgroup X} {t : X} (htK : t ∈ K)
    (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hK2 : ∀ P : Subgroup X, P ≤ K → IsPGroup 2 P → Nat.card P ≤ 2) :
    ∃ N : Subgroup X, N ≤ K ∧ (∀ k ∈ K, (k ∈ N ↔ Odd (orderOf k))) ∧
      ∀ k ∈ K, k ∈ N ∨ k * t ∈ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : ↥K := ⟨t, htK⟩ with ht'def
  have ht'2 : orderOf t' = 2 := by
    apply orderOf_eq_prime
    · rw [sq]; exact Subtype.ext ht2
    · intro h; exact ht1 (congrArg Subtype.val h)
  set P₀ : Subgroup ↥K := zpowers t' with hP₀def
  have hP₀card : Nat.card P₀ = 2 := by rw [hP₀def, Nat.card_zpowers, ht'2]
  have hev : 2 ∣ Nat.card ↥K := by
    rw [← hP₀card]; exact Subgroup.card_subgroup_dvd_card P₀
  have hfac : (Nat.card ↥K).factorization 2 = 1 := by
    have hpos : 0 < (Nat.card ↥K).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hev
    by_contra hne
    have h4 : 2 ^ 2 ∣ Nat.card ↥K :=
      (Nat.pow_dvd_pow 2 (by omega)).trans (Nat.ordProj_dvd _ 2)
    obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
    have hR2 : IsPGroup 2 (R.map K.subtype) := by
      apply IsPGroup.of_card (n := 2)
      rw [Subgroup.card_map_of_injective K.subtype_injective, hR]
    have h1 := hK2 _ (map_subtype_le R) hR2
    rw [Subgroup.card_map_of_injective K.subtype_injective, hR] at h1
    norm_num at h1
  let P : Sylow 2 ↥K := Sylow.ofCard P₀ (by rw [hP₀card, hfac, pow_one])
  have hPcyc : IsCyclic (P : Subgroup ↥K) := by
    change IsCyclic (zpowers t')
    infer_instance
  have hmin : (Nat.card ↥K).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr hev
  set τ := MonoidHom.transferSylow P (hPcyc.normalizer_le_centralizer hmin) with hτdef
  have hcompl : τ.ker.IsComplement' (P : Subgroup ↥K) := hPcyc.isComplement' hmin
  have hodd : ¬ 2 ∣ Nat.card τ.ker := MonoidHom.not_dvd_card_ker_transferSylow P _
  have hmemN : ∀ k : ↥K, k ∈ τ.ker ↔ Odd (orderOf k) := by
    intro k
    constructor
    · intro hk
      have h1 : orderOf (⟨k, hk⟩ : ↥τ.ker) ∣ Nat.card τ.ker := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Nat.odd_iff.mpr (by
        rcases Nat.even_or_odd (orderOf k) with he | ho
        · exact absurd ((even_iff_two_dvd.mp he).trans h1) hodd
        · exact Nat.odd_iff.mp ho)
    · intro hk
      rw [MonoidHom.mem_ker]
      have h1 : orderOf (τ k) ∣ orderOf k := orderOf_map_dvd τ k
      have h2 : orderOf (τ k) ∣ 2 := by
        have h3 := orderOf_dvd_natCard (τ k)
        have h4 : Nat.card (P : Subgroup ↥K) = 2 := hP₀card
        rwa [h4] at h3
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at h1
        have h3 := Nat.odd_iff.mp hk
        omega
  refine ⟨τ.ker.map K.subtype, map_subtype_le _, fun k hk => ?_, fun k hk => ?_⟩
  · constructor
    · rintro ⟨k', hk', rfl⟩
      have h1 := (hmemN k').mp hk'
      rwa [← Subgroup.orderOf_coe] at h1
    · intro hko
      refine ⟨⟨k, hk⟩, (hmemN ⟨k, hk⟩).mpr ?_, rfl⟩
      rwa [Subgroup.orderOf_mk]
  · obtain ⟨⟨⟨n, hn⟩, ⟨p, hp⟩⟩, hnp, -⟩ := hcompl.existsUnique ⟨k, hk⟩
    change n * p = ⟨k, hk⟩ at hnp
    have hp' : p ∈ zpowers t' := hp
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hp'
    have ht'2' : t' * t' = 1 := Subtype.ext ht2
    rcases Int.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · left
      have hj : t' ^ (i + i) = 1 := by
        rw [← two_mul, zpow_mul, zpow_two, ht'2', one_zpow]
      rw [hj, mul_one] at hnp
      exact ⟨n, hn, by rw [hnp]; rfl⟩
    · right
      have hj : t' ^ (2 * i + 1) = t' := by
        rw [zpow_add, zpow_mul, zpow_two, ht'2', one_zpow, one_mul, zpow_one]
      rw [hj] at hnp
      refine ⟨n, hn, ?_⟩
      have h1 : (n : ↥K) = ⟨k, hk⟩ * t' := by
        rw [← hnp, mul_assoc, ht'2', mul_one]
      change ((n : ↥K) : X) = k * t
      rw [h1]
      rfl

end CFSG.ComponentClassification.SolMax
