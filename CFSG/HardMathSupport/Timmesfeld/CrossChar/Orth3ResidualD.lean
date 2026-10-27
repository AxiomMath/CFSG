module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3FamilyD
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Residual

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Timmesfeld.DefChar

@[expose] def regimeDAll3 (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeDOrth idx p ∨ regimeDOrth3Split idx p

@[expose] def regimeTwistedDAll3 (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeTwistedDOrth idx p ∨ regimeTwistedDOrth3Split idx p

theorem crossCharFamAt_D_all3 : CrossCharFamAt .D regimeDAll3 := by
  intro idx hk p hp hp2 hc hR
  rcases hR with hR | hR
  · exact crossCharFamAt_D_orth idx hk p hp hp2 hc hR
  · exact crossCharFamAt_D_orth3_split idx hk p hp hp2 hc hR

theorem crossCharFamAt_twistedD_all3 : CrossCharFamAt .twistedD regimeTwistedDAll3 := by
  intro idx hk p hp hp2 hc hR
  rcases hR with hR | hR
  · exact crossCharFamAt_twistedD_orth idx hk p hp hp2 hc hR
  · exact crossCharFamAt_twistedD_orth3_split idx hk p hp hp2 hc hR

theorem not_regimeDAll3_iff {idx : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : LieFamily.D.Matches idx.1) (hc : idx.1.characteristic ≠ p) :
    ¬ regimeDAll3 idx p ↔ p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .D r q ∧
      (r = 4 ∨ 3 ∣ q.card + 1) := by
  obtain ⟨r, q, hrq⟩ := hk
  have hqp : p ≠ q.p := fun h => hc (by rw [hrq]; simp [h])
  have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp (hrq ▸ idx.2)).1
  unfold regimeDAll3 regimeDOrth regimeDOrth3Split
  constructor
  · intro h
    have hp3 : p = 3 := by
      by_contra hne
      have := hp.two_le
      exact h (Or.inl ⟨r, q, hrq, by omega⟩)
    subst hp3
    refine ⟨rfl, r, q, hrq, ?_⟩
    by_cases hr : r = 4
    · exact Or.inl hr
    · right
      rcases three_dvd_card_sub_or_add_one (q := q) (fun h => hqp h.symm) with h1 | h1
      · exact absurd (Or.inr ⟨r, q, hrq, by omega, rfl, h1⟩) h
      · exact h1
  · rintro ⟨rfl, r', q', hrq', hcond⟩ (⟨r'', q'', hrq'', hp3⟩ | ⟨r'', q'', hrq'', hr5, -, hd⟩)
    · omega
    · rw [hrq] at hrq' hrq''
      obtain ⟨rfl, rfl⟩ : r' = r'' ∧ q' = q'' := by
        injection hrq' with h1 h2
        injection hrq'' with h3 h4
        exact ⟨h1.symm.trans h3, h2.symm.trans h4⟩
      rcases hcond with h | h
      · omega
      · omega

theorem not_regimeTwistedDAll3_iff {idx : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : LieFamily.twistedD.Matches idx.1) (hc : idx.1.characteristic ≠ p) :
    ¬ regimeTwistedDAll3 idx p ↔ p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
      idx.1 = .twistedD r q ∧ 3 ∣ q.card + 1 := by
  obtain ⟨r, q, hrq⟩ := hk
  have hqp : p ≠ q.p := fun h => hc (by rw [hrq]; simp [h])
  unfold regimeTwistedDAll3 regimeTwistedDOrth regimeTwistedDOrth3Split
  constructor
  · intro h
    have hp3 : p = 3 := by
      by_contra hne
      have := hp.two_le
      exact h (Or.inl ⟨r, q, hrq, by omega⟩)
    subst hp3
    refine ⟨rfl, r, q, hrq, ?_⟩
    rcases three_dvd_card_sub_or_add_one (q := q) (fun h => hqp h.symm) with h1 | h1
    · exact absurd (Or.inr ⟨r, q, hrq, rfl, h1⟩) h
    · exact h1
  · rintro ⟨rfl, r', q', hrq', hd⟩ (⟨r'', q'', hrq'', hp3⟩ | ⟨r'', q'', hrq'', -, hd'⟩)
    · omega
    · rw [hrq] at hrq' hrq''
      obtain ⟨rfl, rfl⟩ : r' = r'' ∧ q' = q'' := by
        injection hrq' with h1 h2
        injection hrq'' with h3 h4
        exact ⟨h1.symm.trans h3, h2.symm.trans h4⟩
      omega

end CFSG.HardMathSupport.Timmesfeld.CrossChar
