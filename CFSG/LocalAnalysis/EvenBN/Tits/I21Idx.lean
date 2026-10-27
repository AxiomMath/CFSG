module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Sixteen

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Sec622Bar

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits I21

variable {G : Type} [Group G] [Finite G] {t u x : G}

variable (h : Sec622Bar G t u x)

include h

theorem exists_normal_index_two (S : Sylow 2 G) (hRS : secTwoR t u ≤ S) (hne : secTwoR t u ≠ S) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hdvd : (secTwoR t u).relIndex S ∣ 2 ^ n := by
    have := Subgroup.relIndex_mul_card (secTwoR t u) (S : Subgroup G)
    rw [← hn]
    exact Dvd.intro _ this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · exfalso
      apply hne
      rw [pow_zero, Subgroup.relIndex_eq_one] at hj
      exact le_antisymm hRS hj
    · rw [pow_one] at hj
      obtain ⟨U, hUS, hUrel, hUinv⟩ :=
        h.secTwo.exists_index_two_unique_involution S.isPGroup' hRS hj
      refine exists_normal_index_two_of_free_coset h.secTwo.t_mul_t (U := U) ?_ ?_
      · intro g hg
        have hsq : (g⁻¹ * t * g) ^ 2 = 1 := by
          calc (g⁻¹ * t * g) ^ 2 = g⁻¹ * (t * t) * g := by rw [pow_two]; group
            _ = 1 := by rw [h.secTwo.t_mul_t]; group
        rcases hUinv _ hg hsq with h1 | h1
        · apply h.secTwo.t_ne_one
          calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
            _ = 1 := by rw [h1]; group
        · apply h.secTwo.conj_z_ne_t g
          calc g * u ^ 2 * g⁻¹ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [h1]
            _ = t := by group
      · have h1 := Subgroup.relIndex_mul_index hUS
        have h2 : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
        rw [hUrel] at h1
        omega
  · have hbig : 4 ≤ (secTwoR t u).relIndex S := by
      rw [hj]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact h.exists_normal_index_two_of_big S hRS hbig

end CFSG.LocalAnalysis.EvenBN.Tits.Sec622Bar
