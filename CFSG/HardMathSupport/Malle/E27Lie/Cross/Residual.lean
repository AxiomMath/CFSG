module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.CoveredCert

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.AGLEmbedding TauCeti

@[expose] def IdxChar3 (i : LieTypeIndex) : Prop :=
  (∃ (r : ℕ) (q : PrimePower), q.p = 3 ∧ (i = .A r q ∨ i = .twistedA r q ∨ i = .B r q ∨
    i = .C r q ∨ i = .D r q ∨ i = .twistedD r q)) ∨
  (∃ q : PrimePower, q.p = 3 ∧ (i = .G2 q ∨ i = .F4 q ∨ i = .E6 q ∨ i = .E7 q ∨ i = .E8 q ∨
    i = .twistedE6 q ∨ i = .trialityD4 q)) ∨
  ∃ m : ℕ, i = .reeG2 m

@[expose] def IdxQTwo (i : LieTypeIndex) : Prop :=
  (∃ (r : ℕ) (q : PrimePower), i = .twistedA r q ∧ q.p ^ q.exponent = 2 ∧ 3 ≤ r ∧ r ≤ 8) ∨
  (∃ (r : ℕ) (q : PrimePower), i = .B r q ∧ q.p ^ q.exponent = 2 ∧ (r = 3 ∨ r = 4)) ∨
  (∃ (r : ℕ) (q : PrimePower), i = .D r q ∧ q.p ^ q.exponent = 2 ∧ (r = 4 ∨ r = 5)) ∨
  (∃ (r : ℕ) (q : PrimePower), i = .twistedD r q ∧ q.p ^ q.exponent = 2 ∧ (r = 4 ∨ r = 5))

@[expose] def IdxExcOpen (i : LieTypeIndex) : Prop :=
  (∃ q : PrimePower, q.p ≠ 3 ∧ (i = .G2 q ∨ i = .F4 q ∨ i = .E6 q ∨ i = .E7 q ∨ i = .E8 q ∨
    i = .twistedE6 q ∨ i = .trialityD4 q)) ∨
  ∃ m : ℕ, i = .reeF4 m

theorem card_cases (q : PrimePower) :
    (q.card = 2 ∧ q.p = 2) ∨ (q.card = 3 ∧ q.p = 3) ∨ 4 ≤ q.card := by
  have hp := q.prime_p
  have he := q.exponent_pos
  have hcard : q.p ∣ q.card := by
    rw [PrimePower.card_def]
    exact dvd_pow_self q.p he.ne'
  have h2 : 2 ≤ q.card := by
    rw [PrimePower.card_def]
    exact hp.two_le.trans (Nat.le_self_pow he.ne' q.p)
  by_cases h4 : 4 ≤ q.card
  · exact Or.inr (Or.inr h4)
  · have : q.card = 2 ∨ q.card = 3 := by omega
    rcases this with h | h
    · refine Or.inl ⟨h, ?_⟩
      rw [h] at hcard
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hcard
    · refine Or.inr (Or.inl ⟨h, ?_⟩)
      rw [h] at hcard
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hcard

@[expose] def InnerGoal (i : LieTypeIndex) : Prop :=
  InnerCovered i ∨ InnerCoveredExc i ∨ IdxChar3 i ∨ IdxQTwo i ∨ IdxExcOpen i

section Inj

variable {i : LieTypeIndex}

theorem g_A (h : InnerCoveredA i) : InnerGoal i := Or.inl (Or.inl h)
theorem g_tA (h : InnerCoveredTwistedA i) : InnerGoal i := Or.inl (Or.inr (Or.inl h))
theorem g_Sp (h : InnerCoveredSp i) : InnerGoal i := Or.inl (Or.inr (Or.inr (Or.inl h)))
theorem g_Orth (h : InnerCoveredOrthOdd i) : InnerGoal i :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem g_BCent (h : IdxBCent i) : InnerGoal i :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
theorem g_DCent (h : IdxDCent i) : InnerGoal i :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
theorem g_tDCent (h : IdxTwistedDCent i) : InnerGoal i :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
theorem g_Exc (h : InnerCoveredExc i) : InnerGoal i := Or.inr (Or.inl h)
theorem g_c3 (h : IdxChar3 i) : InnerGoal i := Or.inr (Or.inr (Or.inl h))
theorem g_q2 (h : IdxQTwo i) : InnerGoal i := Or.inr (Or.inr (Or.inr (Or.inl h)))
theorem g_eo (h : IdxExcOpen i) : InnerGoal i := Or.inr (Or.inr (Or.inr (Or.inr h)))

end Inj

theorem inner_exhaustive (d : ValidLieTypeIndex) : InnerGoal d.1 := by
  obtain ⟨i, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hdup := ((LieTypeIndex.valid_iff _).1 hv).2
  rw [LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  show InnerGoal i
  cases i with
  | A r q =>
    simp only at hr hdup
    have hr0 : 1 ≤ r := hr.1
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inl ⟨r, q, hp3, Or.inl rfl⟩)
    refine g_A ⟨r, q, rfl, hp3, ?_⟩
    rcases card_cases q with ⟨hc, -⟩ | ⟨-, hp⟩ | hc
    · rw [PrimePower.card_def] at hc
      have h3 : ¬ (r = 3) := fun h => hdup (Or.inr (Or.inr ⟨h, by simpa using hc⟩))
      have h2 : ¬ (r = 2) := fun h => hdup (Or.inr (Or.inl ⟨h, by simpa using hc⟩))
      have h1 : r = 1 → False := fun h => by
        have := hr.2 h
        simp [PrimePower.card_def, hc] at this
      have hr4 : 4 ≤ r := by
        by_contra hlt
        have : r = 1 ∨ r = 2 ∨ r = 3 := by omega
        rcases this with rfl | rfl | rfl
        exacts [h1 rfl, h2 rfl, h3 rfl]
      exact Or.inr (Or.inr (Or.inl ⟨hr4, hc⟩))
    · exact absurd hp hp3
    · rw [PrimePower.card_def] at hc
      by_cases hr1 : r = 1
      · exact Or.inl hr1
      by_cases hr2 : r = 2
      · exact Or.inr (Or.inr (Or.inr (Or.inl hr2)))
      · exact Or.inr (Or.inl ⟨by omega, hc⟩)
  | twistedA r q =>
    simp only at hr
    have hr0 : 2 ≤ r := hr.1
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inl ⟨r, q, hp3, Or.inr (Or.inl rfl)⟩)
    rcases card_cases q with ⟨hc, -⟩ | ⟨-, hp⟩ | hc
    · rw [PrimePower.card_def] at hc
      by_cases hr9 : 9 ≤ r
      · exact g_tA ⟨r, q, rfl, hp3, Or.inr (Or.inr ⟨hc, hr9⟩)⟩
      · have h2 : r = 2 → False := fun h => by
          have := hr.2 h
          simp [PrimePower.card_def, hc] at this
        have hr3 : 3 ≤ r := by
          by_contra hlt
          have : r = 2 := by omega
          exact h2 this
        exact g_q2 (Or.inl ⟨r, q, rfl, hc, hr3, by omega⟩)
    · exact absurd hp hp3
    · rw [PrimePower.card_def] at hc
      by_cases hr2 : r = 2
      · exact g_tA ⟨r, q, rfl, hp3, Or.inl hr2⟩
      · exact g_tA ⟨r, q, rfl, hp3, Or.inr (Or.inl ⟨hc, by omega⟩)⟩
  | B r q =>
    simp only at hr hdup
    have hr0 : 2 ≤ r := hr.1
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inl ⟨r, q, hp3, Or.inr (Or.inr (Or.inl rfl))⟩)
    by_cases hr2 : r = 2
    · subst hr2
      exact g_Sp (Or.inr (Or.inl ⟨q, rfl, hp3⟩))
    have hr3 : 3 ≤ r := by omega
    by_cases hp2 : q.p = 2
    · rcases card_cases q with ⟨hc, -⟩ | ⟨-, hp⟩ | hc
      · rw [PrimePower.card_def] at hc
        by_cases hr5 : 5 ≤ r
        · refine g_BCent ?_
          simp only [IdxBCent]
          exact ⟨hp2, Or.inr ⟨by simpa using hc, hr5⟩⟩
        · exact g_q2 (Or.inr (Or.inl ⟨r, q, rfl, hc, by omega⟩))
      · exact absurd hp hp3
      · rw [PrimePower.card_def] at hc
        exact g_Sp (Or.inr (Or.inr ⟨r, q, rfl, hp2, hc, hr3⟩))
    · exact g_Orth (Or.inl ⟨r, q, rfl, hp2, hp3, hr3⟩)
  | C r q =>
    simp only at hr
    have hr0 : 3 ≤ r := hr.1
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inl ⟨r, q, hp3, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)
    refine g_Sp (Or.inl ⟨r, q, rfl, hp3, ?_, by omega⟩)
    rcases card_cases q with ⟨-, hp⟩ | ⟨-, hp⟩ | hc
    · exact absurd hp hr.2
    · exact absurd hp hp3
    · rw [PrimePower.card_def] at hc
      exact hc
  | D r q =>
    simp only at hr
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inl ⟨r, q, hp3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩)
    by_cases hp2 : q.p = 2
    · rcases card_cases q with ⟨hc, -⟩ | ⟨-, hp⟩ | hc
      · rw [PrimePower.card_def] at hc
        by_cases hr6 : 6 ≤ r
        · refine g_DCent ?_
          simp only [IdxDCent]
          exact ⟨hp2, Or.inr ⟨by simpa using hc, hr6⟩⟩
        · exact g_q2 (Or.inr (Or.inr (Or.inl ⟨r, q, rfl, hc, by omega⟩)))
      · exact absurd hp hp3
      · refine g_DCent ?_
        simp only [IdxDCent]
        exact ⟨hp2, Or.inl ⟨hc, hr⟩⟩
    · exact g_Orth (Or.inr (Or.inl ⟨r, q, rfl, hp2, hp3⟩))
  | twistedD r q =>
    simp only at hr
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inl ⟨r, q, hp3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩)
    by_cases hp2 : q.p = 2
    · rcases card_cases q with ⟨hc, -⟩ | ⟨-, hp⟩ | hc
      · rw [PrimePower.card_def] at hc
        by_cases hr6 : 6 ≤ r
        · refine g_tDCent ?_
          simp only [IdxTwistedDCent]
          exact ⟨hp2, Or.inr ⟨by simpa using hc, hr6⟩⟩
        · exact g_q2 (Or.inr (Or.inr (Or.inr ⟨r, q, rfl, hc, by omega⟩)))
      · exact absurd hp hp3
      · refine g_tDCent ?_
        simp only [IdxTwistedDCent]
        exact ⟨hp2, Or.inl ⟨hc, hr⟩⟩
    · exact g_Orth (Or.inr (Or.inr ⟨r, q, rfl, hp2, hp3⟩))
  | E6 q =>
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inr (Or.inl ⟨q, hp3, Or.inr (Or.inr (Or.inl rfl))⟩))
    · exact g_eo (Or.inl ⟨q, hp3, Or.inr (Or.inr (Or.inl rfl))⟩)
  | E7 q =>
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inr (Or.inl ⟨q, hp3, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))
    · exact g_eo (Or.inl ⟨q, hp3, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)
  | E8 q =>
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inr (Or.inl ⟨q, hp3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩))
    · exact g_eo (Or.inl ⟨q, hp3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩)
  | F4 q =>
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inr (Or.inl ⟨q, hp3, Or.inr (Or.inl rfl)⟩))
    · exact g_eo (Or.inl ⟨q, hp3, Or.inr (Or.inl rfl)⟩)
  | G2 q =>
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inr (Or.inl ⟨q, hp3, Or.inl rfl⟩))
    · exact g_eo (Or.inl ⟨q, hp3, Or.inl rfl⟩)
  | twistedE6 q =>
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inr (Or.inl ⟨q, hp3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩))
    · exact g_eo (Or.inl ⟨q, hp3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩)
  | trialityD4 q =>
    by_cases hp3 : q.p = 3
    · exact g_c3 (Or.inr (Or.inl ⟨q, hp3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩))
    · exact g_eo (Or.inl ⟨q, hp3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩)
  | suzuki m => exact g_Exc (Or.inl ⟨m, rfl⟩)
  | reeG2 m => exact g_c3 (Or.inr (Or.inr ⟨m, rfl⟩))
  | reeF4 m => exact g_eo (Or.inr ⟨m, rfl⟩)
  | tits => exact g_Exc (Or.inr rfl)

end CFSG.HardMathSupport.Malle.E27Lie
