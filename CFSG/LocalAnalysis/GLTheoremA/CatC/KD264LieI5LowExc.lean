module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem genericOrders_snd_eq_one {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .E6 ∨ t = .twistedE6) (n p f : ℕ) :
    (genericOrders t n p f).2 = 1 := by
  rcases ht with rfl | rfl | rfl | rfl <;> rfl

theorem exceptionalOrders_eq_three_imp {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .E6 ∨ t = .twistedE6) (n p' f : ℕ) :
    ((exceptionalOrders t n p' f).1 = 3 → p' = 3) ∧
      ((exceptionalOrders t n p' f).2 = 3 → p' = 3) := by
  rcases ht with rfl | rfl | rfl | rfl <;> unfold exceptionalOrders <;> split <;>
    simp_all

theorem not_dvd_exceptional {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .E6 ∨ t = .twistedE6) {n p' f : ℕ} (hne : p ≠ p') :
    ¬ p ∣ (exceptionalOrders t n p' f).1 ∧ ¬ p ∣ (exceptionalOrders t n p' f).2 := by
  obtain ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exceptionalOrders_le t n p' f
  have hodd : 3 ≤ p := by have := hp.two_le; omega
  have hsmall : ∀ c : ℕ, 0 < c → c ≤ 4 → (c = 3 → p' = 3) → p ∣ c → False := by
    intro c hc0 hc4 h3 hpc
    have hle : p ≤ c := Nat.le_of_dvd hc0 hpc
    have hp4 : p ≤ 4 := by omega
    interval_cases p
    · have hc3 : c = 3 := by omega
      exact hne (h3 hc3).symm
    · norm_num at hp
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · exact hsmall _ h1 h1' (exceptionalOrders_eq_three_imp ht n p' f).1 hd
  · exact hsmall _ h2 h2' (exceptionalOrders_eq_three_imp ht n p' f).2 hd

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
