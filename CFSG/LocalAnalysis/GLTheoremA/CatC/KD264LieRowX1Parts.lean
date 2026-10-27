module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def KD264X1Concl (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group] : Prop :=
  ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
    IsElemAbelian 3 A →
      CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ CFSG.Open.pRank 3 A →
      ∃ F ≤ A, IsElemAbelian 3 F ∧ min 2 (CFSG.Open.pRank 3 A - 1) ≤ CFSG.Open.pRank 3 F ∧
        IsGood 3 F

@[expose] def KD264X1At (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group] : Prop :=
  ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    ov2Idx d.1 →
    ¬ (∃ n : ℕ, ∃ q : TauCeti.PrimePower, d.1 = .twistedA n q ∧ 3 ∣ n + 1) →
    ¬ (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q) → KD264X1Concl d

theorem kd264X1Row_iff_at :
    KD264X1Row ↔
      ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group], KD264X1At d :=
  Iff.rfl

@[expose] def KD264X1LinPart : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower), d.1 = .A n q →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group], KD264X1At d

@[expose] def KD264X1SpPart : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower), d.1 = .B n q →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group], KD264X1At d

@[expose] def KD264X1OmPlusPart : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower), d.1 = .D n q →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group], KD264X1At d

@[expose] def KD264X1OmMinusPart : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedD n q →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group], KD264X1At d

@[expose] def KD264X1UnPart : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA n q →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group], KD264X1At d

@[expose] def KD264X1ExcPart : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    (d.1 = .E6 q ∨ d.1 = .E7 q ∨ d.1 = .E8 q ∨ d.1 = .F4 q) →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group], KD264X1At d

theorem kd264X1Row_of_parts (hL : KD264X1LinPart) (hSp : KD264X1SpPart)
    (hOp : KD264X1OmPlusPart) (hOm : KD264X1OmMinusPart) (hU : KD264X1UnPart)
    (hE : KD264X1ExcPart) : KD264X1Row := by
  refine kd264X1Row_iff_at.2 ?_
  intro d inst
  obtain ⟨x, hx⟩ := d
  cases x with
  | A n q => exact hL ⟨.A n q, hx⟩ n q rfl
  | twistedA n q => exact hU ⟨.twistedA n q, hx⟩ n q rfl
  | B n q => exact hSp ⟨.B n q, hx⟩ n q rfl
  | D n q => exact hOp ⟨.D n q, hx⟩ n q rfl
  | twistedD n q => exact hOm ⟨.twistedD n q, hx⟩ n q rfl
  | E6 q => exact hE ⟨.E6 q, hx⟩ q (Or.inl rfl)
  | E7 q => exact hE ⟨.E7 q, hx⟩ q (Or.inr (Or.inl rfl))
  | E8 q => exact hE ⟨.E8 q, hx⟩ q (Or.inr (Or.inr (Or.inl rfl)))
  | F4 q => exact hE ⟨.F4 q, hx⟩ q (Or.inr (Or.inr (Or.inr rfl)))
  | C n q =>
    intro _ _ _ h4 _ _
    exfalso
    have hr := ((TauCeti.LieTypeIndex.valid_iff _).1 hx).1
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hr
    simp only [ov2Idx, fieldSize] at h4
    have hp : q.p ∣ 2 := by
      rw [← h4, TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
    have hle : q.p ≤ 2 := Nat.le_of_dvd (by norm_num) hp
    have h2 : q.p = 2 := le_antisymm hle q.prime_p.two_le
    exact hr.2 h2
  | G2 q =>
    intro _ _ _ h4 _ _
    exfalso
    have hr := ((TauCeti.LieTypeIndex.valid_iff _).1 hx).1
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hr
    simp only [ov2Idx, fieldSize] at h4
    omega
  | twistedE6 q =>
    intro _ _ _ _ _ h6
    exact (h6 ⟨q, rfl⟩).elim
  | trialityD4 q =>
    intro _ h2 _ h4 _ _
    exfalso
    apply h2
    simp only [ov2Idx, fieldSize] at h4
    simpa [k2Lie] using h4
  | tits =>
    intro _ h2 _ _ _ _
    exfalso
    exact h2 (by simp [k2Lie])
  | suzuki m =>
    intro _ _ _ h4 _ _
    exfalso
    have hr := ((TauCeti.LieTypeIndex.valid_iff _).1 hx).1
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hr
    simp only [ov2Idx, fieldSize] at h4
    have h1 : 2 * m + 1 = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using h4)
    omega
  | reeF4 m =>
    intro _ _ _ h4 _ _
    exfalso
    have hr := ((TauCeti.LieTypeIndex.valid_iff _).1 hx).1
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hr
    simp only [ov2Idx, fieldSize] at h4
    have h1 : 2 * m + 1 = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using h4)
    omega
  | reeG2 m =>
    intro _ _ _ h4 _ _
    exfalso
    simp only [ov2Idx, fieldSize] at h4
    have h3 : 3 ∣ 2 := by
      rw [← h4]
      exact dvd_pow_self 3 (by omega)
    omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
