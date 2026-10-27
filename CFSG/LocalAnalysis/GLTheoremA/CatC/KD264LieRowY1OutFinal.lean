module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutUniCat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner innAutDerived)

@[expose] def KD264Y1OutFam (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    P d.1 → ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ 3 →
    ∀ a ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group, a ^ 3 = 1 →
      a ∈ inner (TauCeti.CFSGIndex.lie d).Group

@[expose] def KD264Y1OutE6 : Prop :=
  KD264Y1OutFam (fun e => (∃ q : TauCeti.PrimePower, e = TauCeti.LieTypeIndex.E6 q) ∨
    ∃ q : TauCeti.PrimePower, e = TauCeti.LieTypeIndex.twistedE6 q)

@[expose] def KD264Y1OutD4 : Prop :=
  KD264Y1OutFam (fun e => ∃ q : TauCeti.PrimePower, e = TauCeti.LieTypeIndex.D 4 q)

@[expose] def KD264Y1OutOS : Prop :=
  KD264Y1OutFam (fun e =>
    (∃ (r : ℕ) (q : TauCeti.PrimePower), e = TauCeti.LieTypeIndex.B r q) ∨
    (∃ (r : ℕ) (q : TauCeti.PrimePower), e = TauCeti.LieTypeIndex.C r q) ∨
    (∃ (r : ℕ) (q : TauCeti.PrimePower), 5 ≤ r ∧ e = TauCeti.LieTypeIndex.D r q) ∨
    (∃ (r : ℕ) (q : TauCeti.PrimePower), e = TauCeti.LieTypeIndex.twistedD r q))

@[expose] def KD264Y1OutExc : Prop :=
  KD264Y1OutFam (fun e =>
    (∃ q : TauCeti.PrimePower, e = TauCeti.LieTypeIndex.E7 q) ∨
    (∃ q : TauCeti.PrimePower, e = TauCeti.LieTypeIndex.E8 q) ∨
    (∃ q : TauCeti.PrimePower, e = TauCeti.LieTypeIndex.F4 q) ∨
    (∃ q : TauCeti.PrimePower, e = TauCeti.LieTypeIndex.G2 q) ∨
    (∃ k : ℕ, e = TauCeti.LieTypeIndex.reeF4 k) ∨
    (∃ k : ℕ, e = TauCeti.LieTypeIndex.reeG2 k) ∨
    (∃ k : ℕ, e = TauCeti.LieTypeIndex.suzuki k) ∨
    e = TauCeti.LieTypeIndex.tits ∨
    (∃ q : TauCeti.PrimePower, e = TauCeti.LieTypeIndex.trialityD4 q))

theorem KD264Y1Out_of_families (hE6 : KD264Y1OutE6)
    (hD4 : KD264Y1OutD4) (hOS : KD264Y1OutOS) (hExc : KD264Y1OutExc) : KD264Y1Out := by
  intro d hfin hns hk2 hk3 hpR a ha ha3
  rcases d with ⟨e, hv⟩
  have hstd := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases e with
  | A r q => exact kd264Y1OutLin_holds ⟨_, hv⟩ ⟨r, q, rfl⟩ hns hk2 hk3 hpR a ha ha3
  | twistedA r q => exact kd264Y1OutUni_holds ⟨_, hv⟩ ⟨r, q, rfl⟩ hns hk2 hk3 hpR a ha ha3
  | B r q => exact hOS ⟨_, hv⟩ (Or.inl ⟨r, q, rfl⟩) hns hk2 hk3 hpR a ha ha3
  | C r q => exact hOS ⟨_, hv⟩ (Or.inr (Or.inl ⟨r, q, rfl⟩)) hns hk2 hk3 hpR a ha ha3
  | D r q =>
    by_cases hr4 : r = 4
    · subst hr4
      exact hD4 ⟨_, hv⟩ ⟨q, rfl⟩ hns hk2 hk3 hpR a ha ha3
    · have hr5 : 5 ≤ r := by
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hstd
        omega
      exact hOS ⟨_, hv⟩ (Or.inr (Or.inr (Or.inl ⟨r, q, hr5, rfl⟩))) hns hk2 hk3 hpR a ha ha3
  | twistedD r q =>
    exact hOS ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr ⟨r, q, rfl⟩))) hns hk2 hk3 hpR a ha ha3
  | E6 q => exact hE6 ⟨_, hv⟩ (Or.inl ⟨q, rfl⟩) hns hk2 hk3 hpR a ha ha3
  | twistedE6 q => exact hE6 ⟨_, hv⟩ (Or.inr ⟨q, rfl⟩) hns hk2 hk3 hpR a ha ha3
  | E7 q => exact hExc ⟨_, hv⟩ (Or.inl ⟨q, rfl⟩) hns hk2 hk3 hpR a ha ha3
  | E8 q => exact hExc ⟨_, hv⟩ (Or.inr (Or.inl ⟨q, rfl⟩)) hns hk2 hk3 hpR a ha ha3
  | F4 q => exact hExc ⟨_, hv⟩ (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))) hns hk2 hk3 hpR a ha ha3
  | G2 q =>
    exact hExc ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))) hns hk2 hk3 hpR a ha ha3
  | reeF4 k =>
    exact hExc ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, rfl⟩))))) hns hk2 hk3 hpR a ha ha3
  | reeG2 k =>
    exact hExc ⟨_, hv⟩
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, rfl⟩)))))) hns hk2 hk3 hpR a ha ha3
  | suzuki k =>
    exact hExc ⟨_, hv⟩
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, rfl⟩))))))) hns hk2 hk3 hpR a ha ha3
  | tits =>
    exact hExc ⟨_, hv⟩
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) hns hk2 hk3 hpR a ha ha3
  | trialityD4 q =>
    exact hExc ⟨_, hv⟩
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩)))))))) hns hk2 hk3 hpR
        a ha ha3

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
