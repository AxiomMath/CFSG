module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.ShultStronglyClosedTI

variable {A L : Type} [Group A] [Finite A] [Group L] [Finite L]

theorem card_ker_eq_one_or_three [Group.IsPerfect L]
    (hcyc : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → ∀ Q : Sylow q A, IsCyclic (Q : Subgroup A))
    (h3 : ∀ Q : Sylow 3 A, CFSG.Open.IsElemAbelian 3 (Q : Subgroup A) ∧
      Nat.card (Q : Subgroup A) = 9)
    (π : L →* A) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L)
    (hodd : Odd (Nat.card π.ker)) :
    Nat.card π.ker = 1 ∨ Nat.card π.ker = 3 := by
  classical
  have hN0 : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card π.ker → d = 3 := by
    intro d hd hdN
    by_contra hd3
    have : Fact d.Prime := ⟨hd⟩
    have hd2 : d ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdN)
    obtain ⟨C⟩ : Nonempty (Sylow d π.ker) := inferInstance
    obtain ⟨Q⟩ : Nonempty (Sylow d A) := inferInstance
    have hCbot := (small_sylow_central_cover_bound π hπ hker C Q).1 (hcyc d hd hd2 hd3 Q)
    have hcard : Nat.card C = 1 := by
      rw [hCbot]
      exact Subgroup.card_bot
    rw [Sylow.card_eq_multiplicity] at hcard
    have hfac : (Nat.card π.ker).factorization d = 0 := by
      rcases Nat.pow_eq_one.1 hcard with h | h
      · exact absurd h hd.ne_one
      · exact h
    exact (hd.factorization_pos_of_dvd hN0 hdN).ne' hfac
  obtain ⟨k, hk⟩ : ∃ k, Nat.card π.ker = 3 ^ k := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hN0 hall⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C⟩ : Nonempty (Sylow 3 π.ker) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow 3 A) := inferInstance
  have hbound := ((small_sylow_central_cover_bound π hπ hker C Q).2 (h3 Q).1
    (by rw [(h3 Q).2]; norm_num)).2
  have hcard := Sylow.card_eq_multiplicity C
  rw [hk, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same] at hcard
  rw [hcard] at hbound
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k
  · left
    rw [hk]
    rfl
  · right
    rw [hk]
    rfl

end CFSG.QuasithinUnique.Ch1
