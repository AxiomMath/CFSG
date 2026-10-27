module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Family

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Timmesfeld.DefChar

@[expose] def regimeBAll3 (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeBAll idx p ∨ regimeBOrth3Split idx p

theorem crossCharFamAt_B_all3 : CrossCharFamAt .B regimeBAll3 := by
  intro idx hk p hp hp2 hc hR
  rcases hR with hR | hR
  · exact crossCharFamAt_B_all idx hk p hp hp2 hc hR
  · exact crossCharFamAt_B_orth3_split idx hk p hp hp2 hc hR

theorem three_dvd_card_sub_or_add_one {q : TauCeti.PrimePower} (h : q.p ≠ 3) :
    3 ∣ q.card - 1 ∨ 3 ∣ q.card + 1 := by
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have h3 : ¬ 3 ∣ q.card := by
    rw [hq]
    intro hd
    exact h ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)).symm
  have h2 : 2 ≤ q.card := by
    rw [hq]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' _)
  omega

theorem not_regimeBAll3_iff {idx : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : LieFamily.B.Matches idx.1) (hc : idx.1.characteristic ≠ p) :
    ¬ regimeBAll3 idx p ↔ p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧
      ((q.p ≠ 2 ∧ 3 ≤ r ∧ 3 ∣ q.card + 1) ∨ q.card = 2) := by
  obtain ⟨r, q, hrq⟩ := hk
  have hqp : p ≠ q.p := fun h => hc (by rw [hrq]; simp [h])
  unfold regimeBAll3
  rw [not_or]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨h3, r', q', hrq', hcond⟩ := (not_regimeBAll_iff hp hp2 ⟨r, q, hrq⟩).1 h1
    obtain ⟨hrr, hqq⟩ : r' = r ∧ q' = q := by
      rw [hrq] at hrq'
      injection hrq' with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [hrr, hqq] at hcond
    subst h3
    refine ⟨rfl, r, q, hrq, ?_⟩
    rcases hcond with ⟨hq2, hr3⟩ | hq
    · left
      refine ⟨hq2, hr3, ?_⟩
      rcases three_dvd_card_sub_or_add_one (q := q) (fun h => hqp h.symm) with h | h
      · exact absurd ⟨r, q, hrq, hq2, hr3, rfl, h⟩ h2
      · exact h
    · exact Or.inr hq
  · rintro ⟨h3, r', q', hrq', hcond⟩
    subst h3
    obtain ⟨hrr, hqq⟩ : r' = r ∧ q' = q := by
      rw [hrq] at hrq'
      injection hrq' with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [hrr, hqq] at hcond
    refine ⟨(not_regimeBAll_iff hp hp2 ⟨r, q, hrq⟩).2 ⟨rfl, r, q, hrq, ?_⟩, ?_⟩
    · rcases hcond with ⟨hq2, hr3, -⟩ | hq
      · exact Or.inl ⟨hq2, hr3⟩
      · exact Or.inr hq
    · rintro ⟨r'', q'', hrq'', hq2, hr3, -, hd⟩
      rw [hrq] at hrq''
      obtain ⟨hr2, hq2'⟩ : r'' = r ∧ q'' = q := by
        injection hrq'' with h1 h2
        exact ⟨h1.symm, h2.symm⟩
      rw [hq2'] at hd
      rcases hcond with ⟨-, -, hd'⟩ | hq
      · omega
      · rw [hq] at hd; omega

end CFSG.HardMathSupport.Timmesfeld.CrossChar
