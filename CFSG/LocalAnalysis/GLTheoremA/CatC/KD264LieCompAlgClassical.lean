module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonalLie
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

@[expose] def D4EightCompAlgOuter : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, d.1 = .D 4 q) →
    fieldSize d.1 = 8 → CompAlgOuterAt (TauCeti.CFSGIndex.lie d).Group

theorem lieCompAlg_classicalBCD (hD4 : D4EightCompAlgOuter) : LieCompAlg isClassicalBCDIdx := by
  rintro ⟨d, hd⟩ hP hfield
  cases d with
  | B n q =>
    have hq8 : q.p ^ q.exponent = 2 ^ 3 :=
      (TauCeti.PrimePower.card_def q).symm.trans (hfield.trans (by norm_num))
    obtain ⟨hp2, -⟩ := Nat.Prime.pow_inj' q.prime_p Nat.prime_two q.exponent_pos.ne'
      (by norm_num) hq8
    exact lieCompAlg_symplectic ⟨.B n q, hd⟩ (Or.inr hp2) hfield
  | C n q => exact lieCompAlg_symplectic ⟨.C n q, hd⟩ trivial hfield
  | D n q =>
    have h8 : q.p ^ q.exponent = 8 := (TauCeti.PrimePower.card_def q).symm.trans hfield
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D n q hd (MulEquiv.refl _)
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.D n q, hd⟩).Group :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      by_cases h4 : n = 4
      · subst h4
        exact compAlgAt_of_inner_of_outer
          (compAlgInnerAt_of_statedClassicalModel_eight (Or.inr (Or.inl rfl)) hSC h8)
          (hD4 ⟨.D 4 q, hd⟩ ⟨q, rfl⟩ hfield)
      · have h5 : 5 ≤ n := by
          have h4n : 4 ≤ n := hSC.1.2.2
          omega
        exact compAlgAt_pomegaPlus_eight hSC h5 h8
    · have h4n : 4 ≤ n := hadm.2.2
      omega
  | twistedD n q =>
    have h8 : q.p ^ q.exponent = 8 := (TauCeti.PrimePower.card_def q).symm.trans hfield
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD n q hd (MulEquiv.refl _)
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hd⟩).Group :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      exact compAlgAt_pomegaMinus_eight hSC h8
    · have h4n : 4 ≤ n := hadm.2.2
      omega
  | A n q => exact absurd hP (by simp [isClassicalBCDIdx])
  | twistedA n q => exact absurd hP (by simp [isClassicalBCDIdx])
  | E6 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | E7 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | E8 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | F4 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | G2 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | twistedE6 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | trialityD4 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | suzuki k => exact absurd hP (by simp [isClassicalBCDIdx])
  | reeG2 k => exact absurd hP (by simp [isClassicalBCDIdx])
  | reeF4 k => exact absurd hP (by simp [isClassicalBCDIdx])
  | tits => exact absurd hP (by simp [isClassicalBCDIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
