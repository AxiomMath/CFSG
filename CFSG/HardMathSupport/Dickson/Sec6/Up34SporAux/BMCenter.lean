module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.L3Orders
import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.YS08

theorem isPerfect_of_sl3EpsOfChar {p : ℕ} {W : Type} [Group W] (h : SL3EpsOfChar p W) :
    Group.IsPerfect W := by
  rcases h with ⟨K, hF, hfin, -, -, ⟨e⟩⟩ | ⟨K, hF, hfin, q, -, hcard, -, hq2, ⟨e⟩⟩
  · have : Group.IsPerfect (StatedSL 3 K) :=
      CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have := Fintype.ofFinite K
    obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
    have : Fact (ringChar K).Prime := ⟨hp⟩
    have hqd : q ∣ ringChar K ^ (n : ℕ) := by
      rw [← Nat.card_eq_fintype_card, hcard, pow_two] at hn
      exact ⟨q, hn.symm⟩
    obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hqd
    have : Group.IsPerfect (StatedSU 3 (ringChar K ^ f) K) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard le_rfl
        (fun h => hq2 (Prod.ext_iff.1 h).2)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem six_seven_two_zero_mul_center_le_of_isL3Kind {X : Type} [Group X] [Finite X] {p : ℕ}
    (h : IsL3Kind p X) : 6720 * Nat.card ↥(Subgroup.center X) ≤ Nat.card X := by
  have hge := isL3Kind_ge h
  rcases h with hSL | ⟨W, hW, hWSL, ⟨f⟩⟩
  · obtain ⟨hZ3, hbig⟩ := sl3Eps_facts hSL
    omega
  · haveI := isPerfect_of_sl3EpsOfChar hWSL
    have hc : Nat.card ↥(Subgroup.center X) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr f).toEquiv,
        Group.IsPerfect.center_quotient_center_eq_bot W, Subgroup.card_bot]
    omega

end CFSG.HardMathSupport.Dickson.Sec6.BM
