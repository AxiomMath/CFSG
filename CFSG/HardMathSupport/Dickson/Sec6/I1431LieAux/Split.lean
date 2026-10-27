module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Families
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Dickson.Sec6.I923

@[expose] def Y1431LieRestAt (Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Â : Subgroup (MulAut Y)) (ξ : MulAut Y) (J : Subgroup Y)
    (q : ℕ), Y1431Cfg d4Vocab Y Â ξ J q →
    ∀ (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f → t ≠ .Tits → Fam t n p f →
      LieModel (Y ⧸ Subgroup.center Y) t n p f →
      ∀ q0 : ℕ, 4 ≤ q0 → q = q0 ^ 3 → Y1431Concl Y Â ξ J q

@[expose] def Y1431NoCfgAt (Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Â : Subgroup (MulAut Y)) (ξ : MulAut Y) (J : Subgroup Y)
    (q : ℕ), Y1431Cfg d4Vocab Y Â ξ J q →
    ∀ (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f → t ≠ .Tits → Fam t n p f →
      LieModel (Y ⧸ Subgroup.center Y) t n p f →
      ∀ q0 : ℕ, 4 ≤ q0 → q = q0 ^ 3 → False

theorem Y1431NoCfgAt.mono {Fam Fam' : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hle : ∀ t n p f, Fam' t n p f → Fam t n p f) (h : Y1431NoCfgAt Fam) :
    Y1431NoCfgAt Fam' :=
  fun Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq =>
    h Y Â ξ J q c t n p f hadm ht (hle t n p f hF) hm q0 hq0 hqq

theorem Y1431NoCfgAt.of_cover {Fam Fam₁ Fam₂ : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hcov : ∀ t n p f, Fam t n p f → Fam₁ t n p f ∨ Fam₂ t n p f) (h₁ : Y1431NoCfgAt Fam₁)
    (h₂ : Y1431NoCfgAt Fam₂) : Y1431NoCfgAt Fam :=
  fun Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq =>
    (hcov t n p f hF).elim
      (fun hF => h₁ Y Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq)
      (fun hF => h₂ Y Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq)

@[expose] def FamE6Good : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t _ p f => t = .E6 ∧ ¬ 3 ∣ p ^ f - 1

@[expose] def FamE6Bad : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t _ p f => t = .E6 ∧ 3 ∣ p ^ f - 1

@[expose] def FamTwE6Good : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t _ p f => t = .twistedE6 ∧ ¬ 3 ∣ p ^ f + 1

@[expose] def FamTwE6Bad : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t _ p f => t = .twistedE6 ∧ 3 ∣ p ^ f + 1

@[expose] def FamU6Real : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSU ∧ n = 6 ∧ p = 2 ∧ Odd f

@[expose] def FamPsuBadRest : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSU ∧ 3 ≤ n ∧ 3 ∣ Nat.gcd n (p ^ f + 1) ∧ ¬ (n = 6 ∧ p = 2 ∧ Odd f)

theorem fam1431_cover {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (ht : t ≠ .Tits) :
    FamPslTwo t n p f ∨ FamPslGood t n p f ∨ FamPslBad t n p f ∨ FamPsp t n p f ∨
      FamPspTwoEight t n p f ∨ FamPsuGood t n p f ∨ FamPsuBadRest t n p f ∨ FamU6Real t n p f ∨
      FamOrthOdd t n p f ∨ FamOrthPlus t n p f ∨ FamOrthMinus t n p f ∨ FamD4 t n p f ∨
      FamTriD4 t n p f ∨ FamG2 t n p f ∨ FamF4 t n p f ∨ FamE6Good t n p f ∨ FamE6Bad t n p f ∨
      FamTwE6Good t n p f ∨ FamTwE6Bad t n p f ∨ FamE7 t n p f ∨ FamE8 t n p f ∨ FamSz t n p f ∨
      FamReeG2 t n p f ∨ FamReeF4 t n p f := by
  rcases fam_cover hadm ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h
  · exact Or.inl h
  · iterate 1 right
    exact Or.inl h
  · iterate 2 right
    exact Or.inl h
  · iterate 3 right
    exact Or.inl h
  · iterate 4 right
    exact Or.inl h
  · iterate 5 right
    exact Or.inl h
  ·
    by_cases h6 : n = 6 ∧ p = 2 ∧ Odd f
    · iterate 7 right
      exact Or.inl ⟨h.1, h6⟩
    · iterate 6 right
      exact Or.inl ⟨h.1, h.2.1, h.2.2, h6⟩
  · iterate 8 right
    exact Or.inl h
  · iterate 9 right
    exact Or.inl h
  · iterate 10 right
    exact Or.inl h
  · iterate 11 right
    exact Or.inl h
  · iterate 12 right
    exact Or.inl h
  · iterate 13 right
    exact Or.inl h
  · iterate 14 right
    exact Or.inl h
  ·
    by_cases h3 : 3 ∣ p ^ f - 1
    · iterate 16 right
      exact Or.inl ⟨h, h3⟩
    · iterate 15 right
      exact Or.inl ⟨h, h3⟩
  ·
    by_cases h3 : 3 ∣ p ^ f + 1
    · iterate 18 right
      exact Or.inl ⟨h, h3⟩
    · iterate 17 right
      exact Or.inl ⟨h, h3⟩
  · iterate 19 right
    exact Or.inl h
  · iterate 20 right
    exact Or.inl h
  · iterate 21 right
    exact Or.inl h
  · iterate 22 right
    exact Or.inl h
  · iterate 23 right
    exact h

end CFSG.HardMathSupport.Dickson.Sec6.I1431
