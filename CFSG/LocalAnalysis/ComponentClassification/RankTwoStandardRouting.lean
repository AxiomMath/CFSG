module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.ComponentClassification.RankTwoStandard

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def RankTwoRoute (Q : Type) [Group Q] : Prop :=
  RankTwoAlternatingType Q ∨ RankTwoBenderType Q ∨ RankTwoOddLieType Q ∨
    (∃ m : ℕ, 2 ≤ m ∧ StatedClassicalModel Q .PSL 3 2 m) ∨ RankTwoExceptionalEvenType Q ∨
    RankTwoClassicalEvenType Q ∨ NativeSporadic.SporadicRep Q

namespace RankTwoRoute

variable {Q : Type} [Group Q]

theorem of_oddLieType (h : OddLieType Q) : RankTwoRoute Q := by
  by_cases h5 : Nonempty (Q ≃* alternatingGroup (Fin 5))
  · exact Or.inl ⟨5, le_rfl, h5⟩
  by_cases h6 : Nonempty (Q ≃* alternatingGroup (Fin 6))
  · exact Or.inl ⟨6, by norm_num, h6⟩
  by_cases h8 : StatedClassicalModel Q .PSL 2 2 3
  · exact Or.inr (Or.inl (Or.inl ⟨3, le_rfl, h8⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨h, h5, h6, h8⟩))

theorem of_classicalEven
    (h : (∃ n m : ℕ, 4 ≤ n ∧ StatedClassicalModel Q .PSL n 2 m) ∨
      (∃ n m : ℕ, 4 ≤ n ∧ StatedClassicalModel Q .PSU n 2 m) ∨
      (∃ n m : ℕ, 2 ≤ n ∧ StatedClassicalModel Q .PSp n 2 m) ∨
      ∃ n m : ℕ, 4 ≤ n ∧
        (StatedClassicalModel Q .POmegaPlus n 2 m ∨ StatedClassicalModel Q .POmegaMinus n 2 m)) :
    RankTwoRoute Q := by
  by_cases h8 : Nonempty (Q ≃* alternatingGroup (Fin 8))
  · exact Or.inl ⟨8, by norm_num, h8⟩
  by_cases h6 : Nonempty (Q ≃* alternatingGroup (Fin 6))
  · exact Or.inl ⟨6, by norm_num, h6⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, h8, h6⟩)))))

theorem lieModel_of_statedClassicalModel {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel Q t n p f) : LieModel Q t n p f := by
  refine Or.inl ⟨?_, h⟩
  cases t with
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus => decide
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact h.2.elim

theorem of_classical {t : StatedLieTag} {n p f : ℕ} (h : StatedClassicalModel Q t n p f) :
    RankTwoRoute Q := by
  have hadm := h.1
  by_cases hp2 : p ≠ 2
  · exact of_oddLieType ⟨t, n, p, f, hadm.1, hp2, hadm, lieModel_of_statedClassicalModel h⟩
  rw [not_not] at hp2
  subst hp2
  obtain ⟨-, hf1, hcond⟩ := hadm
  cases t with
  | PSL =>
    obtain ⟨hn, h22, -⟩ := hcond
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · interval_cases n
      ·
        have hf2 : f ≠ 1 := by
          rintro rfl
          exact h22 rfl
        rcases Nat.lt_or_ge f 3 with hf3 | hf3
        · obtain rfl : f = 2 := by omega
          exact Or.inl ⟨5, le_rfl,
            CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model Q
              (lieModel_of_statedClassicalModel h)⟩
        · exact Or.inr (Or.inl (Or.inl ⟨f, hf3, h⟩))
      ·
        rcases Nat.lt_or_ge f 2 with hf2 | hf2
        · obtain rfl : f = 1 := by omega
          have h7 := CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism Q
            (lieModel_of_statedClassicalModel h)
          refine of_oddLieType ⟨.PSL, 2, 7, 1, Nat.prime_seven, by norm_num,
            ⟨Nat.prime_seven, le_rfl, ?_⟩, h7⟩
          decide
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf2, h⟩)))
    · exact of_classicalEven (Or.inl ⟨n, f, hn4, h⟩)
  | PSU =>
    obtain ⟨hn, h32⟩ := hcond
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · obtain rfl : n = 3 := by omega
      have hf2 : 2 ≤ f := by
        by_contra hlt
        obtain rfl : f = 1 := by omega
        exact h32 rfl
      exact Or.inr (Or.inl (Or.inr (Or.inl ⟨f, hf2, h⟩)))
    · exact of_classicalEven (Or.inr (Or.inl ⟨n, f, hn4, h⟩))
  | PSp => exact of_classicalEven (Or.inr (Or.inr (Or.inl ⟨n, f, hcond.1, h⟩)))
  | POmegaOdd => exact absurd rfl hcond.2
  | POmegaPlus => exact of_classicalEven (Or.inr (Or.inr (Or.inr ⟨n, f, hcond, Or.inl h⟩)))
  | POmegaMinus => exact of_classicalEven (Or.inr (Or.inr (Or.inr ⟨n, f, hcond, Or.inr h⟩)))
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact h.2.elim

theorem of_chevalleyExceptional {t : StatedLieTag} {p f : ℕ} (ht : t ∈ chevalleyExceptionalTags)
    (h : ChevalleyExceptionalModel Q t p f) : RankTwoRoute Q := by
  have hadm := h.1
  by_cases hp2 : p ≠ 2
  · exact of_oddLieType ⟨t, 0, p, f, hadm.1, hp2, hadm, Or.inr (Or.inl ⟨rfl, ht, h⟩)⟩
  rw [not_not] at hp2
  subst hp2
  have hexc : RankTwoExceptionalEvenType Q := by
    by_cases hG2 : t = .G2
    · subst hG2
      refine Or.inl ⟨f, ?_, h⟩
      obtain ⟨-, hf1, -, h3⟩ := hadm
      by_contra hlt
      obtain rfl : f = 1 := by omega
      norm_num at h3
    · refine Or.inr (Or.inl ⟨t, ?_, f, hadm.2.1, h⟩)
      simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hG2 | decide
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hexc))))

theorem of_reeTits {t : StatedLieTag} {p f : ℕ} (ht : t ∈ reeTitsTags)
    (h : ReeTitsModel Q t p f) : RankTwoRoute Q := by
  have hadm := h.1
  simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  ·
    obtain ⟨hp, -, -, hp3, -⟩ := hadm
    exact of_oddLieType ⟨.twistedG2, 0, p, f, hp, by omega, h.1,
      Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))⟩
  ·
    obtain ⟨-, -, -, hp2, ⟨k, hk⟩, hf3⟩ := hadm
    subst hp2
    subst hk
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨k, by omega, h⟩)))))))
  ·
    obtain ⟨-, -, -, hp2, hf⟩ := hadm
    subst hp2
    subst hf
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr h)))))))

theorem of_suzuki {p f : ℕ} (h : SuzukiModel Q p f) : RankTwoRoute Q := by
  obtain ⟨hp2, a, ha, K, _, _, hf, -⟩ := id h
  subst hp2
  subst hf
  exact Or.inr (Or.inl (Or.inr (Or.inr ⟨a, ha, h⟩)))

end RankTwoRoute

theorem rankTwo_route (Q : Type) [Group Q] (hQ : Catalog Q)
    (hnonab : ∃ a b : Q, a * b ≠ b * a) : RankTwoRoute Q := by
  rcases hQ with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, he⟩ | ⟨t, n, p, f, hm⟩ |
      (⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩) | hs
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd (e.injective (by rw [map_mul, map_mul, mul_comm])) hab
  · exact Or.inl ⟨n, hn, he⟩
  · exact RankTwoRoute.of_classical hm
  · exact RankTwoRoute.of_chevalleyExceptional ht hm
  · exact RankTwoRoute.of_reeTits ht hm
  · exact RankTwoRoute.of_suzuki hm
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs)))))

end CFSG.ComponentClassification.RankTwoStandard
