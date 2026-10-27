module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdReduction
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB

variable {Y : Type} [Group Y]

theorem gsRestricted_odd_family {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : LieModel Y .PSL 2 p (2 * f) ∨ LieModel Y .PSL 3 p f ∨ LieModel Y .PSU 3 p f ∨
      LieModel Y .PSL 4 p f ∨ LieModel Y .PSU 4 p f ∨ LieModel Y .PSp 2 p f ∨
      LieModel Y .POmegaMinus 4 p f) : GSRestricted Y :=
  Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h⟩)

theorem gsRestricted_ree {m : ℕ} (hm : 1 ≤ m) (h : LieModel Y .twistedG2 0 3 (2 * m + 1)) :
    GSRestricted Y :=
  Or.inr (Or.inr (Or.inl ⟨m, hm, h⟩))

theorem gsRestricted_psl_two_sixteen (h : LieModel Y .PSL 2 2 4) : GSRestricted Y :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem gsRestricted_psu_three_four (h : LieModel Y .PSU 3 2 2) : GSRestricted Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem gsRestricted_psp_four_four (h : LieModel Y .PSp 2 2 2) : GSRestricted Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem gsRestricted_psl_five_two (h : LieModel Y .PSL 5 2 1) : GSRestricted Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem gsRestricted_psu_five_two (h : LieModel Y .PSU 5 2 1) : GSRestricted Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem gsRestricted_psl_three_sixteen (h : LieModel Y .PSL 3 2 4) : GSRestricted Y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

theorem gsRestricted_of_isSporadic {s : TauCeti.SporadicName} (hs : s ∈ restrictedSporadicNames)
    (h : NativeSporadic.IsSporadic Y s) : GSRestricted Y := by
  simp only [restrictedSporadicNames, Finset.mem_insert, Finset.mem_singleton] at hs
  unfold GSRestricted
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [h, or_true, true_or]

theorem gsRestricted_odd_psl_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSL 2 p f) (h : LieModel Y .PSL 2 p f) : GSRestricted Y := by
  obtain ⟨-, hf, -, -, h23⟩ := hadm
  refine gsRestricted_psl_two hp hp2 hf ?_ h
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h3 : 3 ≤ p ^ f := by
    have := hp.two_le
    have h3p : 3 ≤ p := by omega
    calc 3 ≤ p := h3p
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  by_contra hlt
  have : p ^ f = 3 ∨ p ^ f = 4 := by omega
  rcases this with h | h
  · exact h23 (by rw [h])
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem gsRestricted_of_alternating {n : ℕ} (hn : 5 ≤ n)
    (h : Nonempty (Y ≃* alternatingGroup (Fin n))) : GSRestricted Y := by
  have hmem : (StatedLieTag.PSL) ∈ classicalTags := by decide
  rcases (show n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | h7
  · have hm := LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five
      Y h
    exact gsRestricted_psl_two Nat.prime_five (by decide) le_rfl (by norm_num) (Or.inl ⟨hmem, hm⟩)
  · have hm := LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six
      Y h
    exact gsRestricted_psl_two Nat.prime_three (by decide) (by norm_num) (by norm_num)
      (Or.inl ⟨hmem, hm⟩)
  · exact gsRestricted_alternating h7 h

theorem lieModel_exceptional_zero {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (h : LieModel Y t n p f) : LieModel Y t 0 p f := by
  have hn : n = 0 := by
    rcases h with ⟨htc, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩
    · exfalso
      simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at htc
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at htc
    all_goals exact hn
  subst hn
  exact h

theorem gsRestricted_or_of_oddLieType (h : OddLieType Y) :
    GSRestricted Y ∨ OddLinearUnrestricted Y ∨ OddClassicalUnrestricted Y ∨
      ExceptionalChevalley Y := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  cases t with
  | PSL =>
    have hn : 2 ≤ n := hadm.2.2.1
    rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | h5
    · exact Or.inl (gsRestricted_odd_psl_two hp hp2 hadm hm)
    · exact Or.inl (gsRestricted_odd_family hp hp2 hf (Or.inr (Or.inl hm)))
    · exact Or.inl (gsRestricted_odd_family hp hp2 hf (Or.inr (Or.inr (Or.inr (Or.inl hm)))))
    · exact Or.inr (Or.inl ⟨n, p, f, hp, hp2, hf, h5, hm⟩)
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
    · exact Or.inl (gsRestricted_odd_family hp hp2 hf (Or.inr (Or.inr (Or.inl hm))))
    · exact Or.inl (gsRestricted_odd_family hp hp2 hf
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))))
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, Or.inl ⟨n, h5, hm⟩⟩))
  | PSp =>
    have hn : 2 ≤ n := hadm.2.2.1
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · exact Or.inl (gsRestricted_odd_family hp hp2 hf
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))))
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inl ⟨n, h3, hm⟩)⟩))
  | POmegaOdd =>
    exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf,
      Or.inr (Or.inr (Or.inl ⟨n, hadm.2.2.1, hm⟩))⟩))
  | POmegaPlus =>
    exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hadm.2.2, hm⟩)))⟩))
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
    · exact Or.inl (gsRestricted_odd_family hp hp2 hf
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm)))))))
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf,
        Or.inr (Or.inr (Or.inr (Or.inr ⟨n, h5, hm⟩)))⟩))
  | G2 => exact Or.inr (Or.inr (Or.inr ⟨.G2, p, f, by decide, hp, hf,
      lieModel_exceptional_zero (by decide) hm⟩))
  | F4 => exact Or.inr (Or.inr (Or.inr ⟨.F4, p, f, by decide, hp, hf,
      lieModel_exceptional_zero (by decide) hm⟩))
  | E6 => exact Or.inr (Or.inr (Or.inr ⟨.E6, p, f, by decide, hp, hf,
      lieModel_exceptional_zero (by decide) hm⟩))
  | E7 => exact Or.inr (Or.inr (Or.inr ⟨.E7, p, f, by decide, hp, hf,
      lieModel_exceptional_zero (by decide) hm⟩))
  | E8 => exact Or.inr (Or.inr (Or.inr ⟨.E8, p, f, by decide, hp, hf,
      lieModel_exceptional_zero (by decide) hm⟩))
  | twistedE6 => exact Or.inr (Or.inr (Or.inr ⟨.twistedE6, p, f, by decide, hp, hf,
      lieModel_exceptional_zero (by decide) hm⟩))
  | trialityD4 => exact Or.inr (Or.inr (Or.inr ⟨.trialityD4, p, f, by decide, hp, hf,
      lieModel_exceptional_zero (by decide) hm⟩))
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2
  | twistedG2 =>
    obtain ⟨-, -, rfl, rfl, ⟨m, rfl⟩, h3⟩ := hadm
    exact Or.inl (gsRestricted_ree (m := m) (by omega) hm)
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2
  | Tits => exact absurd hadm.2.2.2.1 hp2

end CFSG.ComponentClassification.RestrictedStd
