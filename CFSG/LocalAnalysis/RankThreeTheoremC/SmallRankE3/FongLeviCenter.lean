module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

theorem center_eq_bot_of_simple_of_two_le_pRank {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hr : 2 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup G)) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center G := by
        rw [h]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
    letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
    have hprime : (Nat.card G).Prime := IsSimpleGroup.prime_card
    obtain ⟨E, -, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hℓ.one_lt (⊤ : Subgroup G)
    have hE2 : ℓ ^ 2 ∣ Nat.card E := by
      rw [hEcard]
      exact pow_dvd_pow ℓ hr
    have hdvd : ℓ ^ 2 ∣ Nat.card G := hE2.trans (Subgroup.card_subgroup_dvd_card E)
    have hℓG : ℓ ∣ Nat.card G := (dvd_pow_self ℓ two_ne_zero).trans hdvd
    have hℓeq : ℓ = Nat.card G := (Nat.prime_dvd_prime_iff_eq hℓ hprime).1 hℓG
    rw [← hℓeq] at hdvd
    have hle : ℓ ^ 2 ≤ ℓ := Nat.le_of_dvd hℓ.pos hdvd
    have h2 : 2 ≤ ℓ := hℓ.two_le
    nlinarith

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
