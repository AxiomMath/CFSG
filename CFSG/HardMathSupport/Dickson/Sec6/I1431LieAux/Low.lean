module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Rank
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Dickson.Sec6.I923

@[expose] def FamPspLow : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p _ => t = .PSp ∧ n = 2 ∧ p ≠ 3

@[expose] def FamPspHigh : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p _ => t = .PSp ∧ 2 ≤ n ∧ (n ≠ 2 ∨ p = 3)

@[expose] def FamPslGoodThree : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSL ∧ n = 3 ∧ Nat.Coprime 3 (Nat.gcd n (p ^ f - 1)) ∧ p ≠ 3

@[expose] def FamPslGoodHigh : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSL ∧ 3 ≤ n ∧ Nat.Coprime 3 (Nat.gcd n (p ^ f - 1)) ∧ (n ≠ 3 ∨ p = 3)

@[expose] def FamPsuGoodThree : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSU ∧ n = 3 ∧ ¬ 3 ∣ Nat.gcd n (p ^ f + 1) ∧ p ≠ 3

@[expose] def FamPsuGoodHigh : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSU ∧ 3 ≤ n ∧ ¬ 3 ∣ Nat.gcd n (p ^ f + 1) ∧ (n ≠ 3 ∨ p = 3)

@[expose] def FamG2Low : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ p _ => t = .G2 ∧ p ≠ 3

@[expose] def FamG2High : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ p _ => t = .G2 ∧ p = 3

@[expose] def FamTriD4Low : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t _ p _ => t = .trialityD4 ∧ p ≠ 3

@[expose] def FamTriD4High : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t _ p _ => t = .trialityD4 ∧ p = 3

theorem y1431_psp_of_low (h0 : L2CentreThree) (hOut : OutDerived3At FamPspLow)
    (hrk : NoE27At FamPspLow) (hhigh : Y1431NoCfgAt FamPspHigh) : Y1431NoCfgAt FamPsp :=
  Y1431NoCfgAt.of_cover (Fam₁ := FamPspLow) (Fam₂ := FamPspHigh)
    (fun t n p f ⟨ht, hn, _⟩ => by
      by_cases h : n = 2 ∧ p ≠ 3
      · exact Or.inl ⟨ht, h.1, h.2⟩
      · refine Or.inr ⟨ht, hn, ?_⟩
        by_cases h2 : n = 2
        · exact Or.inr (by by_contra h3; exact h ⟨h2, h3⟩)
        · exact Or.inl h2)
    (Y1431NoCfgAt.of_noE27 h0 hOut hrk) hhigh

theorem y1431_pspTwoEight_of_low (h0 : L2CentreThree) (hOut : OutDerived3At FamPspLow)
    (hrk : NoE27At FamPspLow) : Y1431NoCfgAt FamPspTwoEight :=
  (Y1431NoCfgAt.of_noE27 h0 hOut hrk).mono fun t n p f ⟨ht, hn, h8⟩ =>
    ⟨ht, hn, fun hp => by
      subst hp
      have : (3 : ℕ) ^ f % 3 = 8 % 3 := by rw [h8]
      rcases f with _ | f
      · simp at h8
      · rw [pow_succ] at this
        simp [Nat.mul_mod_left] at this⟩

theorem y1431_pslGood_of_low (h0 : L2CentreThree) (hrk : NoE27At FamPslGoodThree)
    (hhigh : Y1431NoCfgAt FamPslGoodHigh) : Y1431NoCfgAt FamPslGood :=
  Y1431NoCfgAt.of_cover (Fam₁ := FamPslGoodThree) (Fam₂ := FamPslGoodHigh)
    (fun t n p f ⟨ht, hn, hc⟩ => by
      by_cases h : n = 3 ∧ p ≠ 3
      · exact Or.inl ⟨ht, h.1, h.1 ▸ hc, h.2⟩
      · refine Or.inr ⟨ht, hn, hc, ?_⟩
        by_cases h3 : n = 3
        · exact Or.inr (by by_contra h4; exact h ⟨h3, h4⟩)
        · exact Or.inl h3)
    (Y1431NoCfgAt.of_noE27 h0
      (outDerived3_pslGood.mono fun t n p f ⟨ht, hn, hc, _⟩ => ⟨ht, by omega, hc⟩) hrk) hhigh

theorem y1431_psuGood_of_low (h0 : L2CentreThree) (hOut : OutDerived3At FamPsuGoodThree)
    (hrk : NoE27At FamPsuGoodThree) (hhigh : Y1431NoCfgAt FamPsuGoodHigh) :
    Y1431NoCfgAt FamPsuGood :=
  Y1431NoCfgAt.of_cover (Fam₁ := FamPsuGoodThree) (Fam₂ := FamPsuGoodHigh)
    (fun t n p f ⟨ht, hn, hc⟩ => by
      by_cases h : n = 3 ∧ p ≠ 3
      · exact Or.inl ⟨ht, h.1, h.1 ▸ hc, h.2⟩
      · refine Or.inr ⟨ht, hn, hc, ?_⟩
        by_cases h3 : n = 3
        · exact Or.inr (by by_contra h4; exact h ⟨h3, h4⟩)
        · exact Or.inl h3)
    (Y1431NoCfgAt.of_noE27 h0 hOut hrk) hhigh

theorem y1431_g2_of_low (h0 : L2CentreThree) (hOut : OutDerived3At FamG2Low)
    (hrk : NoE27At FamG2Low) (hhigh : Y1431NoCfgAt FamG2High) : Y1431NoCfgAt FamG2 :=
  Y1431NoCfgAt.of_cover (Fam₁ := FamG2Low) (Fam₂ := FamG2High)
    (fun t n p f ht => by
      by_cases h : p = 3
      · exact Or.inr ⟨ht, h⟩
      · exact Or.inl ⟨ht, h⟩)
    (Y1431NoCfgAt.of_noE27 h0 hOut hrk) hhigh

theorem y1431_triD4_of_low (h0 : L2CentreThree) (hOut : OutDerived3At FamTriD4Low)
    (hrk : NoE27At FamTriD4Low) (hhigh : Y1431NoCfgAt FamTriD4High) : Y1431NoCfgAt FamTriD4 :=
  Y1431NoCfgAt.of_cover (Fam₁ := FamTriD4Low) (Fam₂ := FamTriD4High)
    (fun t n p f ht => by
      by_cases h : p = 3
      · exact Or.inr ⟨ht, h⟩
      · exact Or.inl ⟨ht, h⟩)
    (Y1431NoCfgAt.of_noE27 h0 hOut hrk) hhigh

theorem y1431_reeF4_of_rank (h0 : L2CentreThree) (hOut : OutDerived3At FamReeF4)
    (hrk : NoE27At FamReeF4) : Y1431NoCfgAt FamReeF4 :=
  Y1431NoCfgAt.of_noE27 h0 hOut hrk

end CFSG.HardMathSupport.Dickson.Sec6.I1431
