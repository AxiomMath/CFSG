module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDAmb

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

section Cover

theorem crossAtOn_of_cover {d : TauCeti.ValidLieTypeIndex} {S S₁ S₂ S₃ : ℕ → Prop}
    (hcov : ∀ p, S p → S₁ p ∨ S₂ p ∨ S₃ p) (h₁ : CrossAtOn d S₁) (h₂ : CrossAtOn d S₂)
    (h₃ : CrossAtOn d S₃) : CrossAtOn d S := by
  refine ⟨fun p hp hp5 hS hdp L _ _ hs hiso hn h2 => ?_,
    fun p hp hp5 hS hdp L _ _ hs hiso hn h3 y hy => ?_⟩
  · rcases hcov p hS with h | h | h
    · exact h₁.1 p hp hp5 h hdp L hs hiso hn h2
    · exact h₂.1 p hp hp5 h hdp L hs hiso hn h2
    · exact h₃.1 p hp hp5 h hdp L hs hiso hn h2
  · rcases hcov p hS with h | h | h
    · exact h₁.2 p hp hp5 h hdp L hs hiso hn h3 y hy
    · exact h₂.2 p hp hp5 h hdp L hs hiso hn h3 y hy
    · exact h₃.2 p hp hp5 h hdp L hs hiso hn h3 y hy

theorem crossAtOn_of_cover2 {d : TauCeti.ValidLieTypeIndex} {S S₁ S₂ : ℕ → Prop}
    (hcov : ∀ p, S p → S₁ p ∨ S₂ p) (h₁ : CrossAtOn d S₁) (h₂ : CrossAtOn d S₂) :
    CrossAtOn d S :=
  crossAtOn_of_cover (S₃ := S₂) (fun p hp => (hcov p hp).elim Or.inl fun h => Or.inr (Or.inr h))
    h₁ h₂ h₂

theorem crossAt_of_le_gt {d : TauCeti.ValidLieTypeIndex} {r : ℕ}
    (h₁ : CrossAtOn d (fun p => p ≤ r)) (h₂ : CrossAtOn d (fun p => r < p)) : CrossAt d := by
  refine ⟨fun p hp hp5 hdp L _ _ hs hiso hn h2 => ?_,
    fun p hp hp5 hdp L _ _ hs hiso hn h3 y hy => ?_⟩
  · rcases le_or_gt p r with h | h
    · exact h₁.1 p hp hp5 h hdp L hs hiso hn h2
    · exact h₂.1 p hp hp5 h hdp L hs hiso hn h2
  · rcases le_or_gt p r with h | h
    · exact h₁.2 p hp hp5 h hdp L hs hiso hn h3 y hy
    · exact h₂.2 p hp hp5 h hdp L hs hiso hn h3 y hy

end Cover

section Props

@[expose] def CrossFamCLarge : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.C r q).Valid),
    CrossAtOn ⟨.C r q, hv⟩ (fun p => ¬ OddOrderAt (q.p ^ q.exponent) p ∧
      ¬ AmbSmallAt (2 * r) (q.p ^ q.exponent) p ∧ p ≤ r)

@[expose] def CrossFamBSpLarge : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B r q).Valid),
    (r = 2 ∨ q.p = 2) →
    CrossAtOn ⟨.B r q, hv⟩ (fun p => ¬ OddOrderAt (q.p ^ q.exponent) p ∧
      ¬ AmbSmallAt (2 * r) (q.p ^ q.exponent) p ∧ p ≤ r)

@[expose] def CrossFamBOrthLarge : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B r q).Valid),
    q.p ≠ 2 → 3 ≤ r →
    CrossAtOn ⟨.B r q, hv⟩ (fun p => ¬ AmbSmallAt (2 * r + 1) (q.p ^ q.exponent) p ∧ p ≤ r)

@[expose] def CrossFamDLarge : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid),
    CrossAtOn ⟨.D r q, hv⟩ (fun p => ¬ AmbSmallAt (2 * r) (q.p ^ q.exponent) p ∧ p ≤ r)

@[expose] def CrossFamTwistedDLarge : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid),
    CrossAtOn ⟨.twistedD r q, hv⟩ (fun p => ¬ AmbSmallAt (2 * r) (q.p ^ q.exponent) p ∧ p ≤ r)

end Props

section Small

theorem crossAtOn_C_le (h : CrossFamCLarge) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) :
    CrossAtOn ⟨.C r q, hv⟩ (fun p => p ≤ r) := by
  refine crossAtOn_of_cover (S₁ := fun p => OddOrderAt (q.p ^ q.exponent) p)
    (S₂ := AmbSmallAt (2 * r) (q.p ^ q.exponent)) (fun p hp => ?_) (crossAtOn_C_odd hv)
    (crossAtOn_C_amb hv) (h r q hv)
  by_cases h1 : OddOrderAt (q.p ^ q.exponent) p
  · exact Or.inl h1
  · by_cases h2 : AmbSmallAt (2 * r) (q.p ^ q.exponent) p
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h1, h2, hp⟩)

theorem crossAtOn_B_le (hsp : CrossFamBSpLarge) (horth : CrossFamBOrthLarge) {r : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B r q).Valid) :
    CrossAtOn ⟨.B r q, hv⟩ (fun p => p ≤ r) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  by_cases hb : r = 2 ∨ q.p = 2
  · refine crossAtOn_of_cover (S₁ := fun p => OddOrderAt (q.p ^ q.exponent) p)
      (S₂ := AmbSmallAt (2 * r) (q.p ^ q.exponent)) (fun p hp => ?_) (crossAtOn_B_sp_odd hv hb)
      (crossAtOn_B_sp_amb hv hb) (hsp r q hv hb)
    by_cases h1 : OddOrderAt (q.p ^ q.exponent) p
    · exact Or.inl h1
    · by_cases h2 : AmbSmallAt (2 * r) (q.p ^ q.exponent) p
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h1, h2, hp⟩)
  · have hq : q.p ≠ 2 := fun h => hb (Or.inr h)
    have hr3 : 3 ≤ r := by omega
    refine crossAtOn_of_cover2 (S₁ := AmbSmallAt (2 * r + 1) (q.p ^ q.exponent))
      (fun p hp => ?_) (crossAtOn_B_amb hv) (horth r q hv hq hr3)
    by_cases h2 : AmbSmallAt (2 * r + 1) (q.p ^ q.exponent) p
    · exact Or.inl h2
    · exact Or.inr ⟨h2, hp⟩

theorem crossAtOn_D_le (h : CrossFamDLarge) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) :
    CrossAtOn ⟨.D r q, hv⟩ (fun p => p ≤ r) := by
  refine crossAtOn_of_cover2 (S₁ := AmbSmallAt (2 * r) (q.p ^ q.exponent)) (fun p hp => ?_)
    (crossAtOn_D_amb hv) (h r q hv)
  by_cases h2 : AmbSmallAt (2 * r) (q.p ^ q.exponent) p
  · exact Or.inl h2
  · exact Or.inr ⟨h2, hp⟩

theorem crossAtOn_twistedD_le (h : CrossFamTwistedDLarge) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) :
    CrossAtOn ⟨.twistedD r q, hv⟩ (fun p => p ≤ r) := by
  refine crossAtOn_of_cover2 (S₁ := AmbSmallAt (2 * r) (q.p ^ q.exponent)) (fun p hp => ?_)
    (crossAtOn_twistedD_amb hv) (h r q hv)
  by_cases h2 : AmbSmallAt (2 * r) (q.p ^ q.exponent) p
  · exact Or.inl h2
  · exact Or.inr ⟨h2, hp⟩

end Small

section Families

theorem crossFamC_of_large
    (hbig : ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.C r q).Valid),
      CrossAtOn ⟨.C r q, hv⟩ (fun p => r < p)) (h : CrossFamCLarge) : CrossFamC :=
  fun r q hv => crossAt_of_le_gt (crossAtOn_C_le h hv) (hbig r q hv)

theorem crossFamB_of_large
    (hbig : ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B r q).Valid),
      CrossAtOn ⟨.B r q, hv⟩ (fun p => r < p)) (hsp : CrossFamBSpLarge)
    (horth : CrossFamBOrthLarge) : CrossFamB :=
  fun r q hv => crossAt_of_le_gt (crossAtOn_B_le hsp horth hv) (hbig r q hv)

theorem crossFamD_of_large
    (hbig : ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid),
      CrossAtOn ⟨.D r q, hv⟩ (fun p => r < p)) (h : CrossFamDLarge) : CrossFamD :=
  fun r q hv => crossAt_of_le_gt (crossAtOn_D_le h hv) (hbig r q hv)

theorem crossFamTwistedD_of_large
    (hbig : ∀ (r : ℕ) (q : TauCeti.PrimePower)
      (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid),
      CrossAtOn ⟨.twistedD r q, hv⟩ (fun p => r < p)) (h : CrossFamTwistedDLarge) :
    CrossFamTwistedD :=
  fun r q hv => crossAt_of_le_gt (crossAtOn_twistedD_le h hv) (hbig r q hv)

end Families

end CFSG.LocalAnalysis.RankFourTheoremC
