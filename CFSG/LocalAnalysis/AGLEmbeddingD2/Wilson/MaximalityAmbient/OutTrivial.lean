module

public import CFSG.Sporadic.Schreier.J4SOutOdd

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_three_dvd_card_outer_J :
    ¬ 3 ∣ Nat.card (Outer J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := CTU_J4_pointwise_local_binary_subgroup_automorphism_kernel_is_two_group.2
  have hCp : ¬ 3 ∣ Nat.card (pointwiseFixingAut H) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  exact not_dvd_card_outer_of_sylow_bound (by omega : 3 ≠ 2) S0Sylow N H
    (by rw [S0Sylow_coe]; exact N_le_S0) (by rw [S0Sylow_coe]; exact S0_le_H) isPGroup_N
    normalizer_N QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2.le hCp
    (R3E_J4_Sylow_two_automorphism_group_is_two_group S0Sylow).2

theorem card_outer_J_eq_one :
    Nat.card (Outer J) = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hdvd
  by_cases h2 : p = 2
  · subst h2
    exact (Nat.not_even_iff_odd.2 CTU_J4_outer_automorphism_group_odd_order)
      (even_iff_two_dvd.2 hdvd)
  by_cases h3 : p = 3
  · subst h3
    exact not_three_dvd_card_outer_J hdvd
  · have h5 : 5 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p <;> first | omega | exact absurd hp (by decide)
      · exact h
    exact not_dvd_card_outer_J hp h5 hdvd

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient
