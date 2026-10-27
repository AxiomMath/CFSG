module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

theorem OddPrimeClassTwoAction.actor_ne_bot {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    (h : OddPrimeClassTwoAction G p P T B e) : B ≠ ⊥ := by
  intro hB
  have h2 : 1 < 2 ^ e - 1 := by
    have h4 : 2 ^ 3 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.two_lt
    omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt h2)
  have hmem : r ∈ piOf B := by
    rw [h.pi_eq]; exact ⟨hr, hrd⟩
  obtain ⟨_, hd⟩ := hmem
  subst hB
  rw [Subgroup.card_bot] at hd
  exact hr.one_lt.ne' (Nat.dvd_one.mp hd)

end CFSG.LocalAnalysis.RankThreeUC.Section5
