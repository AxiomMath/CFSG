module

public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.HardMathSupport.Cooperstein.StructureLie.McLaughlinShape
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusTools

public section

namespace CFSG.GroupTheory

open scoped Pointwise

variable {R : Type} [Group R] [Finite R]

theorem permuting_sylow_order_eight (P : Sylow 2 R)
    (hP8 : Nat.card (P : Subgroup R) = 8) {A N : Subgroup R}
    (hperm : (A : Set R) * ((P : Subgroup R) : Set R) = ((P : Subgroup R) : Set R) * (A : Set R))
    (hNA : N ≤ A) (hNn : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (hN2 : IsPGroup 2 N)
    (h4 : 4 * Nat.card N ∣ Nat.card A) (hperf : ⁅A, A⁆ ⊔ N = A) :
    Nat.card N ≤ 2 ∧ N ≤ (P : Subgroup R) ∧
      ∀ B : Subgroup R, B ≤ A ⊔ (P : Subgroup R) → Nat.card B = Nat.card A → B = A := by
  classical
  have hNnorm : (N.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr
      (Subgroup.le_normalizer_iff.mpr hNn)
  have hNsub2 : IsPGroup 2 (N.subgroupOf A) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNA).symm
  have hPrelOdd : ¬ 2 ∣ (P : Subgroup R).relIndex (A ⊔ (P : Subgroup R)) :=
    fun h => P.not_dvd_index
      (h.trans (Subgroup.relIndex_dvd_index_of_le
        (le_sup_right : (P : Subgroup R) ≤ A ⊔ (P : Subgroup R))))
  have hPsubOdd : ¬ 2 ∣ ((P : Subgroup R).subgroupOf A).index := by
    show ¬ 2 ∣ (P : Subgroup R).relIndex A
    rw [← CFSG.ABGTheoremB.TotallyInverted.Omnibus.relIndex_sup_of_mul_comm hperm]
    exact hPrelOdd
  have hPsub2 : IsPGroup 2 ((P : Subgroup R).subgroupOf A) :=
    P.isPGroup'.comap_of_injective A.subtype A.subtype_injective
  let S : Sylow 2 ↥A := hPsub2.toSylow hPsubOdd
  have hScoe : (S : Subgroup ↥A) = (P : Subgroup R).subgroupOf A :=
    IsPGroup.toSylow_coe hPsub2 hPsubOdd
  have hPsubcard : Nat.card ↥((P : Subgroup R).subgroupOf A) =
      Nat.card ↥(A ⊓ (P : Subgroup R)) := by
    rw [← Subgroup.inf_subgroupOf_left (H := (P : Subgroup R)) (K := A)]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := A ⊓ (P : Subgroup R)) (K := A) inf_le_left).toEquiv
  have hNP : N ≤ (P : Subgroup R) := by
    intro n hn
    have h1 : (⟨n, hNA hn⟩ : ↥A) ∈ N.subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      exact hn
    have h2 : (⟨n, hNA hn⟩ : ↥A) ∈ (S : Subgroup ↥A) :=
      IsPGroup.le_sylow_of_normal hNsub2 S h1
    rw [hScoe, Subgroup.mem_subgroupOf] at h2
    exact h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN2
  have h4dvd : 2 ^ (k + 2) ∣ Nat.card ↥A := by
    have h4eq : 4 * Nat.card N = 2 ^ (k + 2) := by
      rw [hk, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_comm]
    rwa [h4eq] at h4
  have hpowdvd : 2 ^ (k + 2) ∣ Nat.card ↥(A ⊓ (P : Subgroup R)) := by
    have hSdvd : 2 ^ (k + 2) ∣ Nat.card ↥(S : Subgroup ↥A) :=
      Sylow.pow_dvd_card_of_pow_dvd_card S h4dvd
    rw [hScoe, hPsubcard] at hSdvd
    exact hSdvd
  have hinfdvd8 : Nat.card ↥(A ⊓ (P : Subgroup R)) ∣ 8 := by
    have h := Subgroup.card_dvd_of_le
      (H := A ⊓ (P : Subgroup R)) (K := (P : Subgroup R)) inf_le_right
    simpa [hP8] using h
  have hNcard : Nat.card N ≤ 2 := by
    have h2dvd8 : 2 ^ (k + 2) ∣ 8 := hpowdvd.trans hinfdvd8
    have h2le : 2 ^ (k + 2) ≤ 2 ^ 3 := by simpa using Nat.le_of_dvd (by norm_num) h2dvd8
    have hk2 : k + 2 ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2le
    have hk1 : k ≤ 1 := by omega
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hk1
      _ = 2 := by norm_num
  refine ⟨hNcard, hNP, ?_⟩
  intro B hBle hBcard
  by_cases hPA : (P : Subgroup R) ≤ A
  · have hAP : A ⊔ (P : Subgroup R) = A := sup_eq_left.mpr hPA
    rw [hAP] at hBle
    exact Subgroup.eq_of_le_of_card_ge hBle (by rw [hBcard])
  ·
    have hPnotle : ¬ (P : Subgroup R) ≤ A := hPA
    have hinf4 : Nat.card ↥(A ⊓ (P : Subgroup R)) = 4 := by
      have h8not : Nat.card ↥(A ⊓ (P : Subgroup R)) ≠ 8 := by
        intro h8
        apply hPnotle
        have hEq : A ⊓ (P : Subgroup R) = (P : Subgroup R) :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h8, hP8])
        rw [← hEq]
        exact inf_le_left
      have h4le : 4 ≤ Nat.card ↥(A ⊓ (P : Subgroup R)) := by
        have h2 : 2 ^ 2 ≤ 2 ^ (k + 2) :=
          (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr (by omega)
        exact h2.trans (Nat.le_of_dvd Nat.card_pos hpowdvd)
      have h8dvd : Nat.card ↥(A ⊓ (P : Subgroup R)) ∣ 2 ^ 3 := by
        simpa using hinfdvd8
      obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h8dvd
      have hj2 : 2 ≤ j := by
        by_contra h
        have h1 : j ≤ 1 := by omega
        have h2 : 2 ^ j ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr h1
        rw [hj] at h4le
        omega
      have hjne : j ≠ 3 := by
        intro h3
        apply h8not
        rw [hj, h3]
        norm_num
      have hjeq : j = 2 := by omega
      rw [hj, hjeq]
      norm_num
    have hrelP : (P : Subgroup R).relIndex (A ⊔ (P : Subgroup R)) =
        (A ⊓ (P : Subgroup R)).relIndex A := by
      rw [CFSG.ABGTheoremB.TotallyInverted.Omnibus.relIndex_sup_of_mul_comm hperm]
      exact (Subgroup.inf_relIndex_left (H := A) (K := (P : Subgroup R))).symm
    have hPcardEq : (P : Subgroup R).relIndex (A ⊔ (P : Subgroup R)) * 8 =
        Nat.card ↥(A ⊔ (P : Subgroup R)) := by
      have h1 := Subgroup.relIndex_mul_card
        (H := (P : Subgroup R)) (K := A ⊔ (P : Subgroup R))
      rw [inf_eq_left.mpr (le_sup_right : (P : Subgroup R) ≤ A ⊔ (P : Subgroup R)),
        hP8] at h1
      exact h1
    have hAcardEq : (A ⊓ (P : Subgroup R)).relIndex A * 4 = Nat.card A := by
      have h1 := Subgroup.relIndex_mul_card
        (H := A ⊓ (P : Subgroup R)) (K := A)
      rw [inf_eq_left.mpr (inf_le_left : A ⊓ (P : Subgroup R) ≤ A), hinf4] at h1
      exact h1
    have hAPcard : Nat.card ↥(A ⊔ (P : Subgroup R)) = 2 * Nat.card A := by
      have h2 : (P : Subgroup R).relIndex (A ⊔ (P : Subgroup R)) * 4 = Nat.card A := by
        rw [hrelP]
        exact hAcardEq
      calc Nat.card ↥(A ⊔ (P : Subgroup R)) =
          (P : Subgroup R).relIndex (A ⊔ (P : Subgroup R)) * 8 := hPcardEq.symm
        _ = 2 * ((P : Subgroup R).relIndex (A ⊔ (P : Subgroup R)) * 4) := by ring
        _ = 2 * Nat.card A := by rw [h2]
    have hArel2 : A.relIndex (A ⊔ (P : Subgroup R)) = 2 := by
      have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ (P : Subgroup R))
      rw [inf_eq_left.mpr (le_sup_left : A ≤ A ⊔ (P : Subgroup R)), hAPcard] at h1
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    have hAnormal : (A.subgroupOf (A ⊔ (P : Subgroup R))).Normal :=
      Subgroup.normal_of_index_eq_two hArel2
    have hAPnorm : A ⊔ (P : Subgroup R) ≤ Subgroup.normalizer (A : Set R) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (le_sup_left : A ≤ A ⊔ (P : Subgroup R))).mp hAnormal
    by_cases hBA : B ≤ A
    · exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hBcard])
    · rw [SetLike.le_def] at hBA
      obtain ⟨b, hbB, hbA⟩ : ∃ b, b ∈ B ∧ b ∉ A := by
        by_contra h
        apply hBA
        intro x hx
        by_contra hxA
        exact h ⟨x, hx, hxA⟩
      have hproper : A < A ⊔ B := by
        refine lt_of_le_of_ne (le_sup_left : A ≤ A ⊔ B) ?_
        intro heq
        exact hbA (heq.symm ▸ Subgroup.mem_sup_right hbB)
      have hdvd2 : Nat.card ↥(A ⊔ B) ∣ 2 * Nat.card A := by
        rw [← hAPcard]
        exact Subgroup.card_dvd_of_le
          (sup_le (le_sup_left : A ≤ A ⊔ (P : Subgroup R)) hBle)
      have hABcard : Nat.card ↥(A ⊔ B) = 2 * Nat.card A := by
        have hdle : Nat.card ↥(A ⊔ B) ≤ 2 * Nat.card A :=
          Nat.le_of_dvd (Nat.mul_pos (by norm_num) Nat.card_pos) hdvd2
        have hlt : Nat.card A < Nat.card ↥(A ⊔ B) := Subgroup.card_lt_of_lt hproper
        have hdiv1 : 2 * Nat.card A / Nat.card ↥(A ⊔ B) = 1 :=
          Nat.div_eq_of_lt_le (by simpa using hdle) (by omega)
        exact Nat.eq_of_dvd_of_div_eq_one hdvd2 hdiv1
      have hBrel2 : B.relIndex (A ⊔ B) = 2 := by
        have h1 := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
        rw [inf_eq_left.mpr (le_sup_right : B ≤ A ⊔ B), hABcard, hBcard] at h1
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
      have hBnorm : B ≤ Subgroup.normalizer (A : Set R) := hBle.trans hAPnorm
      have hrelB := (relIndex_sup_eq_relIndex_inf_of_le_normalizer
        (H := B) (K := A) hBnorm).1
      have hinfrel : (A ⊓ B).relIndex A = 2 := by
        rw [inf_comm B A, sup_comm B A] at hrelB
        exact hrelB.symm.trans hBrel2
      have hNbot : N = ⊥ := by
        have hdvd4 : 2 ^ (k + 2) ∣ 4 := by
          rw [← hinf4]
          exact hpowdvd
        have h2le : 2 ^ (k + 2) ≤ 2 ^ 2 := by
          simpa using Nat.le_of_dvd (by norm_num) hdvd4
        have hk0 : k = 0 := by
          have : k + 2 ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2le
          omega
        apply Subgroup.eq_bot_of_card_eq
        rw [hk, hk0]
        norm_num
      have hperfA : ⁅A, A⁆ = A := by simpa [hNbot] using hperf
      exact (CFSG.HardMathSupport.Cooperstein.StructureLie.false_of_perfect_of_relIndex_two
        hinfrel hperfA).elim

end CFSG.GroupTheory

end
