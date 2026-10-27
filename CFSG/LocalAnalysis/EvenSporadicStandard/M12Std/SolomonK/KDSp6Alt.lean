module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.BasicSylow

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup

theorem alt_two_part_eq_nine {n : ℕ} (hn : 5 ≤ n)
    (h : (Nat.card (alternatingGroup (Fin n))).factorization 2 = 9) : n = 12 ∨ n = 13 := by
  have hn2 : 2 ≤ n := by omega
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
  have hcard : 2 * Nat.card (alternatingGroup (Fin n)) = Nat.factorial n := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  have hc0 : Nat.card (alternatingGroup (Fin n)) ≠ 0 := by
    intro h0
    have : Nat.factorial n = 0 := by rw [← hcard, h0, mul_zero]
    exact Nat.factorial_ne_zero n this
  have h29 : 2 ^ 9 ∣ Nat.card (alternatingGroup (Fin n)) := by
    rw [Nat.prime_two.pow_dvd_iff_le_factorization hc0]
    omega
  have h210 : ¬ 2 ^ 10 ∣ Nat.card (alternatingGroup (Fin n)) := by
    rw [Nat.prime_two.pow_dvd_iff_le_factorization hc0]
    omega
  have h210dvd : 2 ^ 10 ∣ 2 * Nat.card (alternatingGroup (Fin n)) := by
    have h := mul_dvd_mul_left 2 h29
    rwa [show (2 : ℕ) * 2 ^ 9 = 2 ^ 10 by norm_num] at h
  have hnfact : 2 ^ 10 ∣ Nat.factorial n := by
    rw [← hcard]
    exact h210dvd
  rcases le_or_gt n 11 with hn11 | hn11
  · exact absurd (dvd_trans hnfact (Nat.factorial_dvd_factorial hn11)) (by decide)
  · by_cases hn13 : n ≤ 13
    · omega
    · rw [not_le] at hn13
      have h14 : (2 : ℕ) ^ 11 ∣ Nat.factorial 14 := by decide
      have hdvd14 : Nat.factorial 14 ∣ Nat.factorial n := Nat.factorial_dvd_factorial (by omega)
      have h211 : 2 ^ 11 ∣ Nat.factorial n := dvd_trans h14 hdvd14
      have h210' : 2 ^ 10 ∣ Nat.card (alternatingGroup (Fin n)) := by
        have h : 2 ^ 11 ∣ 2 * Nat.card (alternatingGroup (Fin n)) := by
          rwa [← hcard] at h211
        have h' : 2 * 2 ^ 10 ∣ 2 * Nat.card (alternatingGroup (Fin n)) := by
          rwa [show (2 : ℕ) ^ 11 = 2 * 2 ^ 10 by norm_num] at h
        exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp h'
      exact absurd h210' h210

theorem card_normalizer_map {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (E : Subgroup K) :
    Nat.card (normalizer ((E.map e.toMonoidHom : Subgroup K') : Set K')) =
      Nat.card (normalizer (E : Set K)) := by
  rw [← Subgroup.map_equiv_normalizer_eq E e, Subgroup.card_map_of_injective e.injective]

variable {K : Type} [Group K] [Finite K]

theorem false_of_alternating (hP : P12Facts) (hK : SolomonA12HypK K) {n : ℕ} (hn : 5 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) : False := by
  have h2K : (Nat.card K).factorization 2 = 9 := two_part_card hP hK
  have hcardK : Nat.card K = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
  have h2n : (Nat.card (alternatingGroup (Fin n))).factorization 2 = 9 := by
    rw [← hcardK]
    exact h2K
  rcases alt_two_part_eq_nine hn h2n with hn12 | hn13
  · subst n
    obtain ⟨E, hE⟩ := hK.exists_goodE
    let E' : Subgroup (alternatingGroup (Fin 12)) := E.map e.toMonoidHom
    have hsq' : ∀ x ∈ E', x * x = 1 := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa using congrArg e.toMonoidHom (hE.sq y hy)
    have hcard' : Nat.card E' = 2 ^ 6 := by
      change Nat.card (E.map e.toMonoidHom) = 2 ^ 6
      rw [Subgroup.card_map_of_injective e.injective, hE.card]
    have h9 := hP.alt12 E' hsq' hcard'
    have hnorm : Nat.card (normalizer (E' : Set (alternatingGroup (Fin 12)))) =
        Nat.card (normalizer (E : Set K)) := card_normalizer_map e E
    rw [hnorm, hE.card_normalizer] at h9
    exact absurd h9 (by norm_num)
  · subst n
    obtain ⟨E, hE⟩ := hK.exists_goodE
    let E' : Subgroup (alternatingGroup (Fin 13)) := E.map e.toMonoidHom
    have hsq' : ∀ x ∈ E', x * x = 1 := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa using congrArg e.toMonoidHom (hE.sq y hy)
    have hcard' : Nat.card E' = 2 ^ 6 := by
      change Nat.card (E.map e.toMonoidHom) = 2 ^ 6
      rw [Subgroup.card_map_of_injective e.injective, hE.card]
    have h9 := hP.alt13 E' hsq' hcard'
    have hnorm : Nat.card (normalizer (E' : Set (alternatingGroup (Fin 13)))) =
        Nat.card (normalizer (E : Set K)) := card_normalizer_map e E
    rw [hnorm, hE.card_normalizer] at h9
    exact absurd h9 (by norm_num)

end CFSG.EvenSporadicStandard.M12Std.SolomonK
