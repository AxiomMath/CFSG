module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieProfile

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem lie_nine_survivors {N : ℕ} {d : TauCeti.ValidLieTypeIndex} (h : LieListProfile 3 N d)
    (h5 : ¬ 3 ^ 5 ∣ N) (hA : 181440 ∣ N) :
    N = 1451520 ∨ (N = 1056706560 ∧ IsSpFourEightIndex d) := by
  cases h with
  | linTwo m hm hd hN =>
    have hm5 : m < 5 := by
      by_contra hc
      exact h5 ((pow_dvd_pow 3 (by omega)).trans (hN ▸ Dvd.intro _ rfl))
    rw [hN] at hA
    interval_cases m <;> exact absurd hA (by decide)
  | unitary a ha hd hfe hN =>
    have h3 : 3 ^ (3 * a) ∣ N := by
      rw [hN]
      have := pow_dvd_ordTwistedA_two (3 ^ a) (Nat.one_le_pow _ _ (by norm_num))
      rwa [← pow_mul, mul_comm] at this
    have ha2 : a < 2 := by
      by_contra hc
      exact h5 ((pow_dvd_pow 3 (by omega)).trans h3)
    obtain rfl : a = 1 := by omega
    rw [hN] at hA
    exact absurd hA (by decide)
  | ree a hp ha hd hfe hN =>
    refine absurd ((pow_dvd_pow 3 (by omega : 5 ≤ 3 * a)).trans ?_) h5
    rw [hN]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    rw [← pow_mul, mul_comm]
  | spFour hN =>
    rw [hN] at hA
    exact absurd hA (by decide)
  | chevThree hp hN hD4 hSp hE6 =>
    simp only [chevThreeOrders, List.mem_cons, List.not_mem_nil, or_false] at hN
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact Or.inl rfl
      | exact Or.inr ⟨rfl, hSp rfl⟩
      | exact absurd (by decide) h5
      | exact absurd hA (by decide)
  | reeFFive hp hN => omega

end CFSG.AGLEmbedding
