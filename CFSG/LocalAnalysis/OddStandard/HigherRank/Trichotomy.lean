module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves

public section

namespace CFSG.OddStandard.HigherRank

open CFSG.Open CFSG.Yardstones.M0362f3a873a3

theorem eq_three_of_pow_lt_five {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : p ^ f < 5) : p = 3 ∧ f = 1 := by
  have hp5 : p < 5 := lt_of_le_of_lt (Nat.le_self_pow (by omega) p) h
  have hp3 : p = 3 := by
    have h2 := hp.two_le
    interval_cases p
    · exact absurd rfl hp2
    · rfl
    · exact absurd hp (by norm_num)
  subst hp3
  refine ⟨rfl, ?_⟩
  by_contra hne
  have h9 : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem hr_trichotomy {Q : Type} [Group Q] (hodd : CFSG.Blueprint.OddLieType Q)
    (hF3 : ¬ SmallF3LieQuotient Q) (hL2 : ¬ L2OrReeLieQuotient Q) :
    HRClassical Q ∨ HRF3HigherRank Q ∨ HRG23 Q := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  have hf : 1 ≤ f := hadm.2.1
  have hadm' := hadm.2.2
  by_cases h5 : 5 ≤ p ^ f
  · left
    refine ⟨t, n, p, f, hp, hp2, hadm, hm, ?_, ?_, Or.inl h5⟩
    · cases t <;> first | trivial | skip
      · obtain ⟨-, rfl, -⟩ := hadm'
        exact absurd rfl hp2
      · obtain ⟨rfl, rfl, -⟩ := hadm'
        exact absurd (Or.inr ⟨f, hm⟩) hL2
      · obtain ⟨-, rfl, -⟩ := hadm'
        exact absurd rfl hp2
      · obtain ⟨-, rfl, -⟩ := hadm'
        exact absurd rfl hp2
    · rintro ⟨rfl, rfl⟩
      exact hL2 (Or.inl ⟨p, f, hm⟩)
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_lt_five hp hp2 hf (by omega)
    cases t with
    | PSL =>
      obtain ⟨hn, -, h23⟩ := hadm'
      have hn2 : n ≠ 2 := fun h => h23 (by subst h; rfl)
      by_cases hn5 : 5 ≤ n
      · exact Or.inr (Or.inl ⟨.PSL, n, hm, Or.inl ⟨rfl, hn5⟩⟩)
      · exfalso
        have : n = 3 ∨ n = 4 := by omega
        rcases this with rfl | rfl
        · exact hF3 (Or.inl hm)
        · exact hF3 (Or.inr (Or.inr (Or.inr (Or.inl hm))))
    | PSU =>
      obtain ⟨hn, -⟩ := hadm'
      by_cases hn5 : 5 ≤ n
      · exact Or.inr (Or.inl ⟨.PSU, n, hm, Or.inr (Or.inl ⟨rfl, hn5⟩)⟩)
      · exfalso
        have : n = 3 ∨ n = 4 := by omega
        rcases this with rfl | rfl
        · exact hF3 (Or.inr (Or.inl hm))
        · exact hF3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))
    | PSp =>
      obtain ⟨hn, -⟩ := hadm'
      by_cases hn3 : 3 ≤ n
      · exact Or.inr (Or.inl ⟨.PSp, n, hm, Or.inr (Or.inr (Or.inl ⟨rfl, hn3⟩))⟩)
      · exfalso
        have : n = 2 := by omega
        subst this
        exact hF3 (Or.inr (Or.inr (Or.inl hm)))
    | POmegaOdd =>
      obtain ⟨hn, -⟩ := hadm'
      by_cases hn4 : 4 ≤ n
      · exact Or.inr (Or.inl ⟨.POmegaOdd, n, hm, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn4⟩)))⟩)
      · exfalso
        have : n = 3 := by omega
        subst this
        exact hF3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))))
    | POmegaPlus =>
      by_cases hn5 : 5 ≤ n
      · exact Or.inr (Or.inl ⟨.POmegaPlus, n, hm,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn5⟩))))⟩)
      · exfalso
        have : n = 4 := by omega
        subst this
        exact hF3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))))
    | POmegaMinus =>
      by_cases hn5 : 5 ≤ n
      · exact Or.inr (Or.inl ⟨.POmegaMinus, n, hm,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn5⟩)))))⟩)
      · exfalso
        have : n = 4 := by omega
        subst this
        exact hF3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm)))))))
    | G2 =>
      obtain ⟨rfl, -⟩ := hadm'
      exact Or.inr (Or.inr hm)
    | F4 =>
      obtain rfl := hadm'
      exact Or.inr (Or.inl ⟨.F4, 0, hm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl rfl))))))⟩)
    | E6 =>
      obtain rfl := hadm'
      exact Or.inr (Or.inl ⟨.E6, 0, hm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl rfl)))))))⟩)
    | E7 =>
      obtain rfl := hadm'
      exact Or.inr (Or.inl ⟨.E7, 0, hm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl rfl))))))))⟩)
    | E8 =>
      obtain rfl := hadm'
      exact Or.inr (Or.inl ⟨.E8, 0, hm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))⟩)
    | twistedE6 =>
      obtain rfl := hadm'
      exact Or.inr (Or.inl ⟨.twistedE6, 0, hm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))⟩)
    | trialityD4 =>
      exact Or.inl ⟨.trialityD4, n, 3, 1, hp, hp2, hadm, hm, trivial, by simp, Or.inr rfl⟩
    | twistedB2 =>
      obtain ⟨-, h, -⟩ := hadm'
      omega
    | twistedG2 =>
      obtain ⟨-, -, -, h⟩ := hadm'
      omega
    | twistedF4 =>
      obtain ⟨-, h, -⟩ := hadm'
      omega
    | Tits =>
      obtain ⟨-, h, -⟩ := hadm'
      omega

end CFSG.OddStandard.HigherRank
