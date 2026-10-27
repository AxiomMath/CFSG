module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFFrontier
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Ln

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.Assembly.LowTwoRank TauCeti

theorem isClassicalTwoOrG2_lie_A1_small {q : PrimePower}
    (hv : (LieTypeIndex.A 1 q).Valid) (h : q.card = 5 ∨ q.card = 7 ∨ q.card = 9) :
    CFSG.AGLEmbedding.IsClassicalTwoOrG2 (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group := by
  have hm := statedClassicalModel_PSL_of_lieA hv
    (MulEquiv.refl (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm.2
  have hKq : Nat.card K = q.card := by rw [hK, PrimePower.card_def]
  rcases h with h5 | h7 | h9
  · refine Or.inr (Or.inl ⟨5, Or.inl rfl, ?_⟩)
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
      (Or.inr (hKq.trans h5))
    exact ⟨e.trans e5⟩
  · exact Or.inr (Or.inr ⟨⟨.A 1 q, hv⟩, Or.inl ⟨q, h7, rfl⟩, ⟨MulEquiv.refl _⟩⟩)
  · refine Or.inr (Or.inl ⟨6, Or.inr (Or.inl rfl), ?_⟩)
    obtain ⟨e6⟩ := CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine
      (F := K) (hKq.trans h9)
    exact ⟨(e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans e6⟩

theorem valid_lie_A_range {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid) :
    1 ≤ r ∧ (r = 1 → 4 ≤ q.card) :=
  (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1

theorem prime_five_or_seven {p : ℕ} (hp : p.Prime) (h4 : 4 ≤ p) (h11 : p < 11) :
    p = 5 ∨ p = 7 := by
  interval_cases p <;> first | omega | (exfalso; revert hp; decide)

theorem noFFModule_lie_A_of_odd_of
    (hLn : ∀ (d : ValidLieTypeIndex) {r : ℕ} {q : PrimePower}, d.1 = .A r q → q.p ≠ 2 →
      2 ≤ r → ¬ (r = 2 ∧ q.exponent = 1) → NoFFModule (CFSGIndex.lie d).Group)
    (d : ValidLieTypeIndex) {r : ℕ} {q : PrimePower} (hd : d.1 = .A r q) (hp : q.p ≠ 2)
    (hc : ¬ CFSG.AGLEmbedding.IsClassicalTwoOrG2 (CFSGIndex.lie d).Group)
    (hs : ¬ IsSQTKOddLieIndex d.1) : NoFFModule (CFSGIndex.lie d).Group := by
  have hLn' := hLn d hd hp
  obtain ⟨d, hv⟩ := d
  simp only at hd hs
  subst hd
  have hr := valid_lie_A_range hv
  have hcard : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hpp := q.prime_p
  have hepos := q.exponent_pos
  by_cases hr1 : r = 1
  · subst hr1
    by_cases he3 : 3 ≤ q.exponent
    · exact noFFModule_lie_A1 ⟨.A 1 q, hv⟩ rfl hp he3
    · exfalso
      have he : q.exponent = 1 ∨ q.exponent = 2 := by omega
      have h4 := hr.2 rfl
      rcases he with he | he
      · rw [hcard, he, pow_one] at h4
        by_cases h11 : 11 ≤ q.p
        · exact hs (Or.inl ⟨he, h11⟩)
        · rcases prime_five_or_seven hpp h4 (by omega) with h5 | h7
          · exact hc (isClassicalTwoOrG2_lie_A1_small hv
              (Or.inl (by rw [hcard, he, pow_one, h5])))
          · exact hc (isClassicalTwoOrG2_lie_A1_small hv
              (Or.inr (Or.inl (by rw [hcard, he, pow_one, h7]))))
      · by_cases h5 : 5 ≤ q.p
        · exact hs (Or.inr ⟨he, h5⟩)
        · have h3 : q.p = 3 := by
            have h2 := hpp.two_le
            have h4' : q.p ≠ 4 := by
              intro h
              rw [h] at hpp
              exact absurd hpp (by decide)
            omega
          exact hc (isClassicalTwoOrG2_lie_A1_small hv
            (Or.inr (Or.inr (by rw [hcard, he, h3]; norm_num))))
  · have hr2 : 2 ≤ r := by omega
    by_cases h21 : r = 2 ∧ q.exponent = 1
    · exfalso
      apply hs
      obtain ⟨rfl, he⟩ := h21
      exact ⟨he, hp⟩
    · exact hLn' hr2 h21

@[expose] def GF2NoFFLieOddNonA : Prop :=
  ∀ d : ValidLieTypeIndex, (∀ (r : ℕ) (q : PrimePower), d.1 ≠ .A r q) →
    d.1.characteristic ≠ 2 → ¬ CFSG.AGLEmbedding.IsClassicalTwoOrG2 (CFSGIndex.lie d).Group →
      ¬ IsSQTKOddLieIndex d.1 → NoFFModule (CFSGIndex.lie d).Group

theorem gf2NoFFLieOdd_of_nonA_of
    (hLn : ∀ (d : ValidLieTypeIndex) {r : ℕ} {q : PrimePower}, d.1 = .A r q → q.p ≠ 2 →
      2 ≤ r → ¬ (r = 2 ∧ q.exponent = 1) → NoFFModule (CFSGIndex.lie d).Group)
    (h : GF2NoFFLieOddNonA) : GF2NoFFLieOdd := by
  intro d hchar hc hs
  by_cases hA : ∃ (r : ℕ) (q : PrimePower), d.1 = .A r q
  · obtain ⟨r, q, hd⟩ := hA
    have hp : q.p ≠ 2 := by
      rw [hd, LieTypeIndex.characteristic_A] at hchar
      exact hchar
    exact noFFModule_lie_A_of_odd_of hLn d hd hp hc hs
  · exact h d (fun r q hd => hA ⟨r, q, hd⟩) hchar hc hs

theorem gf2NoFFLieOdd_of_nonA (h : GF2NoFFLieOddNonA) :
    GF2NoFFLieOdd :=
  gf2NoFFLieOdd_of_nonA_of noFFModule_lie_A h

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
