module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxD4
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


theorem lieCompIdx_classicalBCD : LieCompIdx isClassicalBCDIdx := by
  rintro ⟨d, hd⟩ p hp hp2 hpc hP
  cases d with
  | B n q =>
    by_cases hB : n = 2 ∨ q.p = 2
    · exact compIdxAt_psp hp hp2 (d := ⟨.B n q, hd⟩) hB hpc
    ·
      push_neg at hB
      change p ≠ (TauCeti.LieTypeIndex.B n q).characteristic at hpc
      rw [TauCeti.LieTypeIndex.characteristic_B] at hpc
      have hn3 : 3 ≤ n := by
        have h2n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hd).1).1
        omega
      have hSC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd n q hd hB.2 hn3
        (MulEquiv.refl _)
      haveI : Finite (TauCeti.CFSGIndex.lie ⟨.B n q, hd⟩).Group :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      exact compIdxAt_pomegaOdd hSC hp hp2 hpc q.card_def
  | C n q => exact compIdxAt_psp hp hp2 (d := ⟨.C n q, hd⟩) trivial hpc
  | D n q =>
    by_cases h4 : n = 4
    · subst h4
      exact compIdxAt_D4 q hd hp hp2 hpc
    · change p ≠ (TauCeti.LieTypeIndex.D n q).characteristic at hpc
      rw [TauCeti.LieTypeIndex.characteristic_D] at hpc
      obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D n q hd (MulEquiv.refl _)
      · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.D n q, hd⟩).Group :=
          CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
        have h5 : 5 ≤ n := by
          have h4n : 4 ≤ n := hSC.1.2.2
          omega
        exact compIdxAt_pomegaPlus hSC h5 hp hp2 hpc q.card_def
      · have h4n : 4 ≤ n := hadm.2.2
        omega
  | twistedD n q =>
    change p ≠ (TauCeti.LieTypeIndex.twistedD n q).characteristic at hpc
    rw [TauCeti.LieTypeIndex.characteristic_twistedD] at hpc
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD n q hd (MulEquiv.refl _)
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hd⟩).Group :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      exact compIdxAt_pomegaMinus hSC hp hp2 hpc q.card_def
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
