module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.RankThree.PartOne

theorem exists_sylow_le_of_isStronglyPEmbedded {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) {Y : Subgroup Q} (hY : IsStronglyPEmbedded p Y) :
    ∃ S : Sylow p Q, (S : Subgroup Q) ≤ Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, hPY⟩ := hY.exists_isSylowOf_le
  refine ⟨hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2), ?_⟩
  simpa using hPY

theorem pow_dvd_card_inf_of_normal {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {Y : Subgroup Q} (hY : ∃ S : Sylow p Q, (S : Subgroup Q) ≤ Y) (N : Subgroup Q) [N.Normal] :
    p ^ (Nat.card N).factorization p ∣ Nat.card ↥(Y ⊓ N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSY⟩ := hY
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p (S : Subgroup Q) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup',
      by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have hinf : CFSG.ABGLocalTools.IsSylowOf p ((S : Subgroup Q) ⊓ N) N :=
    hSyl.inf_of_le_normalizer le_top (by simp [Subgroup.normalizer_eq_top])
  have hcard : Nat.card ↥((S : Subgroup Q) ⊓ N) = p ^ (Nat.card N).factorization p :=
    hinf.card_eq
  exact hcard ▸ Subgroup.card_dvd_of_le (inf_le_inf hSY le_rfl)

theorem false_of_normal_card_six_or_one_twenty {Q : Type*} [Group Q] [Finite Q]
    {Y : Subgroup Q} (hY : IsStronglyPEmbedded 3 Y)
    (hS : ∃ S : Sylow 2 Q, (S : Subgroup Q) ≤ Y) (N : Subgroup Q) [N.Normal]
    (hN : Nat.card N = 6 ∨ Nat.card N = 120) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S3, hS3Y⟩ := exists_sylow_le_of_isStronglyPEmbedded Nat.prime_three hY
  let m : ℕ := Nat.card ↥(Y ⊓ N)
  have hdvd : m ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_right
  have hcop23 : Nat.Coprime 2 3 :=
    (Nat.coprime_primes Nat.prime_two Nat.prime_three).mpr (by norm_num)
  rcases hN with hN | hN
  ·
    have h2 : 2 ^ (Nat.card N).factorization 2 ∣ m :=
      pow_dvd_card_inf_of_normal Nat.prime_two hS N
    have h3 : 3 ^ (Nat.card N).factorization 3 ∣ m :=
      pow_dvd_card_inf_of_normal Nat.prime_three ⟨S3, hS3Y⟩ N
    have h2exp : 1 ≤ (Nat.card N).factorization 2 := by
      rw [hN]
      exact (Nat.prime_two.dvd_iff_one_le_factorization (by norm_num)).mp (by norm_num)
    have h3exp : 1 ≤ (Nat.card N).factorization 3 := by
      rw [hN]
      exact (Nat.prime_three.dvd_iff_one_le_factorization (by norm_num)).mp (by norm_num)
    have h2dvd : 2 ∣ m := by
      simpa using (pow_dvd_pow 2 h2exp).trans h2
    have h3dvd : 3 ∣ m := by
      simpa using (pow_dvd_pow 3 h3exp).trans h3
    have hm6 : m = 6 := by
      have h6dvd : 6 ∣ m := by
        simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop23 h2dvd h3dvd
      have hmle : m ≤ 6 := by
        have h := hdvd
        rw [hN] at h
        exact Nat.le_of_dvd (by norm_num) h
      have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hdvd (by rw [hN]; norm_num)
      have h6le : 6 ≤ m := Nat.le_of_dvd hmpos h6dvd
      omega
    have hle : N ≤ Y := by
      have hcardle : Nat.card N ≤ m := by simp [hN, hm6]
      exact inf_eq_right.mp (Subgroup.eq_of_le_of_card_ge inf_le_right hcardle)
    exact hY.not_dvd_card_of_normal_le hle (by rw [hN]; norm_num)
  ·
    have h2 : 2 ^ (Nat.card N).factorization 2 ∣ m :=
      pow_dvd_card_inf_of_normal Nat.prime_two hS N
    have h3 : 3 ^ (Nat.card N).factorization 3 ∣ m :=
      pow_dvd_card_inf_of_normal Nat.prime_three ⟨S3, hS3Y⟩ N
    have h2exp : 3 ≤ (Nat.card N).factorization 2 := by
      rw [hN]
      exact (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mp (by norm_num)
    have h3exp : 1 ≤ (Nat.card N).factorization 3 := by
      rw [hN]
      exact (Nat.prime_three.dvd_iff_one_le_factorization (by norm_num)).mp (by norm_num)
    have h8dvd : 8 ∣ m := by
      simpa using (pow_dvd_pow 2 h2exp).trans h2
    have h3dvd : 3 ∣ m := by
      simpa using (pow_dvd_pow 3 h3exp).trans h3
    have hcop83 : Nat.Coprime 8 3 := by
      simpa using Nat.coprime_pow_primes 3 1 Nat.prime_two Nat.prime_three (by norm_num)
    have h24dvd : 24 ∣ m := by
      simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop83 h8dvd h3dvd
    by_cases hNY : N ≤ Y
    · exact hY.not_dvd_card_of_normal_le hNY (by rw [hN]; norm_num)
    · have hm24 : m = 24 := by
        obtain ⟨k, hk⟩ := h24dvd
        have hk5 : k ∣ 5 := by
          have hdiv : 24 * k ∣ 120 := by
            have h := hdvd
            rw [hN] at h
            rwa [hk] at h
          obtain ⟨j, hj⟩ := hdiv
          refine ⟨j, ?_⟩
          have h24k5 : 24 * (k * j) = 24 * 5 := by
            rw [← mul_assoc, hj.symm]
          exact (Nat.mul_left_cancel (by norm_num : 0 < 24) h24k5).symm
        rcases (Nat.dvd_prime Nat.prime_five).mp hk5 with hk1 | hk5'
        · rw [hk, hk1, mul_one]
        · exfalso
          apply hNY
          have hm120 : m = 120 := by rw [hk, hk5']
          have hcardle : Nat.card N ≤ m := by simp [hN, hm120]
          exact inf_eq_right.mp (Subgroup.eq_of_le_of_card_ge inf_le_right hcardle)
      have h3N : 3 ∣ Nat.card ↥(N ⊓ Y) := by rw [inf_comm]; exact h3dvd
      let Y₁ : Subgroup ↥N := (N ⊓ Y).subgroupOf N
      have hY₁ : IsStronglyPEmbedded 3 Y₁ := hY.subgroupOf hNY h3N
      have hcardY₁ : Nat.card ↥Y₁ = 24 := by
        have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ Y ≤ N)).toEquiv
        change Nat.card ↥((N ⊓ Y).subgroupOf N) = 24
        rw [h]
        rw [inf_comm]
        exact hm24
      have hindex : Y₁.index * 24 = 120 := by
        have h := Subgroup.index_mul_card (H := Y₁)
        rw [hcardY₁] at h
        rw [hN] at h
        exact h
      have hidx5 : Y₁.index = 5 := by omega
      obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' 3 hY₁.2.1
      have hx3 : (x : ↥N) ^ 3 = 1 := by
        have hx3' : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
        simpa using congrArg (fun y : ↥Y₁ => (y : ↥N)) hx3'
      let R : Subgroup ↥N := Subgroup.zpowers (x : ↥N)
      have hRne : R ≠ ⊥ := by
        change Subgroup.zpowers (x : ↥N) ≠ ⊥
        rw [Ne, Subgroup.zpowers_eq_bot]
        intro hx1
        have horder : orderOf (x : ↥N) = 3 := by rw [Subgroup.orderOf_coe, hxord]
        rw [hx1, orderOf_one] at horder
        exact absurd horder (by norm_num)
      have hRp : IsPGroup 3 R :=
        CFSG.RankThree.PartOne.StrongP.isPGroup_zpowers_of_pow_eq_one hx3
      have hRle : R ≤ Y₁ := Subgroup.zpowers_le.mpr x.2
      have hmod := hY₁.index_modEq hRne hRp hRle
      rw [hidx5] at hmod
      norm_num [Nat.ModEq] at hmod

end CFSG.GroupTheory.ThreeTranspositions
