module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3FamilyQ

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Timmesfeld.DefChar

@[expose] def regimeBAll4 (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeBAll3 idx p ∨ regimeBOrth3Nonsplit idx p

@[expose] def regimeDAll4 (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeDAll3 idx p ∨ regimeDOrth3Nonsplit idx p

@[expose] def regimeTwistedDAll4 (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeTwistedDAll3 idx p ∨ regimeTwistedDOrth3Nonsplit idx p

theorem crossCharFamAt_B_all4 : CrossCharFamAt .B regimeBAll4 := by
  intro idx hk p hp hp2 hc hR
  rcases hR with hR | hR
  · exact crossCharFamAt_B_all3 idx hk p hp hp2 hc hR
  · exact crossCharFamAt_B_orth3_nonsplit idx hk p hp hp2 hc hR

theorem crossCharFamAt_D_all4 : CrossCharFamAt .D regimeDAll4 := by
  intro idx hk p hp hp2 hc hR
  rcases hR with hR | hR
  · exact crossCharFamAt_D_all3 idx hk p hp hp2 hc hR
  · exact crossCharFamAt_D_orth3_nonsplit idx hk p hp hp2 hc hR

theorem crossCharFamAt_twistedD_all4 : CrossCharFamAt .twistedD regimeTwistedDAll4 := by
  intro idx hk p hp hp2 hc hR
  rcases hR with hR | hR
  · exact crossCharFamAt_twistedD_all3 idx hk p hp hp2 hc hR
  · exact crossCharFamAt_twistedD_orth3_nonsplit idx hk p hp hp2 hc hR

theorem primePower_p_eq_two_of_card_eq_two {q : TauCeti.PrimePower} (h : q.card = 2) :
    q.p = 2 := by
  rw [TauCeti.PrimePower.card_def] at h
  have : q.p ∣ 2 := h ▸ dvd_pow_self q.p q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this

theorem not_regimeBAll4_iff {idx : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : LieFamily.B.Matches idx.1) (hc : idx.1.characteristic ≠ p) :
    ¬ regimeBAll4 idx p ↔ p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧
      q.card = 2 := by
  obtain ⟨r, q, hrq⟩ := hk
  unfold regimeBAll4
  rw [not_or, not_regimeBAll3_iff hp hp2 ⟨r, q, hrq⟩ hc]
  constructor
  · rintro ⟨⟨h3, r', q', hrq', hcond⟩, hn⟩
    subst h3
    obtain ⟨hr, hq⟩ : r' = r ∧ q' = q := by
      rw [hrq] at hrq'
      injection hrq' with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [hr, hq] at hcond
    refine ⟨rfl, r, q, hrq, ?_⟩
    rcases hcond with ⟨hq2, hr3, hd⟩ | h
    · exact absurd ⟨r, q, hrq, hq2, hr3, rfl, hd⟩ hn
    · exact h
  · rintro ⟨h3, r', q', hrq', hq2⟩
    subst h3
    obtain ⟨hr, hq⟩ : r' = r ∧ q' = q := by
      rw [hrq] at hrq'
      injection hrq' with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [hq] at hq2
    refine ⟨⟨rfl, r, q, hrq, Or.inr hq2⟩, ?_⟩
    rintro ⟨r'', q'', hrq'', hq2'', -, -, hd⟩
    rw [hrq] at hrq''
    obtain ⟨-, hq⟩ : r'' = r ∧ q'' = q := by
      injection hrq'' with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [hq] at hq2''
    exact hq2'' (primePower_p_eq_two_of_card_eq_two hq2)

theorem not_regimeDAll4_iff {idx : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : LieFamily.D.Matches idx.1) (hc : idx.1.characteristic ≠ p) :
    ¬ regimeDAll4 idx p ↔ p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .D r q ∧
      (r = 4 ∨ q.card = 2) := by
  obtain ⟨r, q, hrq⟩ := hk
  unfold regimeDAll4
  rw [not_or, not_regimeDAll3_iff hp hp2 ⟨r, q, hrq⟩ hc]
  constructor
  · rintro ⟨⟨h3, r', q', hrq', hcond⟩, hn⟩
    subst h3
    obtain ⟨hr, hq⟩ : r' = r ∧ q' = q := by
      rw [hrq] at hrq'
      injection hrq' with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [hr, hq] at hcond
    refine ⟨rfl, r, q, hrq, ?_⟩
    rcases hcond with h | hd
    · exact Or.inl h
    · by_cases hr4 : r = 4
      · exact Or.inl hr4
      · by_cases hq2 : q.card = 2
        · exact Or.inr hq2
        · have hr4' : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
            ((TauCeti.LieTypeIndex.valid_iff _).mp (hrq ▸ idx.2)).1
          exact absurd ⟨r, q, hrq, by omega, rfl, hd, hq2⟩ hn
  · rintro ⟨h3, r', q', hrq', hcond⟩
    subst h3
    obtain ⟨hr, hq⟩ : r' = r ∧ q' = q := by
      rw [hrq] at hrq'
      injection hrq' with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [hr, hq] at hcond
    have hqp : 3 ≠ q.p := fun h => hc (by rw [hrq]; simp [h])
    refine ⟨⟨rfl, r, q, hrq, ?_⟩, ?_⟩
    · rcases hcond with h | h
      · exact Or.inl h
      · right
        rcases three_dvd_card_sub_or_add_one (q := q) (fun h => hqp h.symm) with h1 | h1
        · have h2 : 2 ≤ q.card := by
            rw [TauCeti.PrimePower.card_def]
            exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' _)
          omega
        · exact h1
    · rintro ⟨r'', q'', hrq'', hr5, -, hd, hq2⟩
      rw [hrq] at hrq''
      obtain ⟨hr2, hq3⟩ : r'' = r ∧ q'' = q := by
        injection hrq'' with h1 h2
        exact ⟨h1.symm, h2.symm⟩
      rw [hr2] at hr5
      rw [hq3] at hq2
      rcases hcond with h | h
      · omega
      · exact hq2 h

theorem not_regimeTwistedDAll4_iff {idx : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : LieFamily.twistedD.Matches idx.1) (hc : idx.1.characteristic ≠ p) :
    ¬ regimeTwistedDAll4 idx p ↔ p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
      idx.1 = .twistedD r q ∧ q.card = 2 := by
  obtain ⟨r, q, hrq⟩ := hk
  unfold regimeTwistedDAll4
  rw [not_or, not_regimeTwistedDAll3_iff hp hp2 ⟨r, q, hrq⟩ hc]
  constructor
  · rintro ⟨⟨h3, r', q', hrq', hd⟩, hn⟩
    subst h3
    obtain ⟨hr, hq⟩ : r' = r ∧ q' = q := by
      rw [hrq] at hrq'
      injection hrq' with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [hq] at hd
    refine ⟨rfl, r, q, hrq, ?_⟩
    by_contra hq2
    exact hn ⟨r, q, hrq, rfl, hd, hq2⟩
  · rintro ⟨h3, r', q', hrq', hq2⟩
    subst h3
    obtain ⟨hr, hq⟩ : r' = r ∧ q' = q := by
      rw [hrq] at hrq'
      injection hrq' with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [hq] at hq2
    refine ⟨⟨rfl, r, q, hrq, ?_⟩, ?_⟩
    · omega
    · rintro ⟨r'', q'', hrq'', -, hd, hq2'⟩
      rw [hrq] at hrq''
      obtain ⟨-, hq3⟩ : r'' = r ∧ q'' = q := by
        injection hrq'' with h1 h2
        exact ⟨h1.symm, h2.symm⟩
      rw [hq3] at hq2'
      exact hq2' hq2

theorem crossCharFamAt_not_regimeBAll4_iff :
    CrossCharFamAt .B (fun idx p => ¬ regimeBAll4 idx p) ↔
      CrossCharFamAt .B (fun idx p => p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
        idx.1 = .B r q ∧ q.card = 2) := by
  constructor
  · intro h idx hk p hp hp2 hc hR
    exact h idx hk p hp hp2 hc ((not_regimeBAll4_iff hp hp2 hk hc).2 hR)
  · intro h idx hk p hp hp2 hc hR
    exact h idx hk p hp hp2 hc ((not_regimeBAll4_iff hp hp2 hk hc).1 hR)

theorem crossCharFamAt_not_regimeTwistedDAll4_iff :
    CrossCharFamAt .twistedD (fun idx p => ¬ regimeTwistedDAll4 idx p) ↔
      CrossCharFamAt .twistedD (fun idx p => p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
        idx.1 = .twistedD r q ∧ q.card = 2) := by
  constructor
  · intro h idx hk p hp hp2 hc hR
    exact h idx hk p hp hp2 hc ((not_regimeTwistedDAll4_iff hp hp2 hk hc).2 hR)
  · intro h idx hk p hp hp2 hc hR
    exact h idx hk p hp hp2 hc ((not_regimeTwistedDAll4_iff hp hp2 hk hc).1 hR)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
