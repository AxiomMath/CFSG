module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxOrthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxD4Three

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem lieOuterIdx_classicalBCD :
    LieOuterIdx isClassicalBCDIdx := by
  rintro ⟨d, hd⟩ p hp hp2 hpc hP hpdvd -
  cases d with
  | B n q =>
    change p ≠ (TauCeti.LieTypeIndex.B n q).characteristic at hpc
    rw [TauCeti.LieTypeIndex.characteristic_B] at hpc
    haveI : Finite (TauCeti.CFSGIndex.lie ⟨.B n q, hd⟩).Group := by
      rcases CFSG.Models.lieModel_B n q hd (MulEquiv.refl _) with
        ⟨hadm, hSC | ⟨h0, -⟩⟩ | ⟨hadm, hSC | ⟨h0, -⟩⟩
      · exact CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      · have h2n : 2 ≤ n := hadm.2.2.1
        omega
      · exact CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      · have h3n : 3 ≤ n := hadm.2.2.1
        omega
    by_cases hB : n = 2 ∨ q.p = 2
    · exact outerIdxAt_B_PSp hp hp2 hd hB (MulEquiv.refl _) hpc hpdvd
    ·
      push_neg at hB
      have hn3 : 3 ≤ n := by
        have h2n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hd).1).1
        omega
      have hSC : CFSG.Open.StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.B n q, hd⟩).Group
          .POmegaOdd n q.p q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, hn3, hB.2⟩, _, inferInstance,
          CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _,
          CFSG.Models.card_fixedField_of (TauCeti.LieTypeIndex.characteristic_B n q)
            (TauCeti.LieTypeIndex.fieldExponent_B n q),
          ⟨CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n q hd hB.2
            hn3⟩⟩
      exact outerIdxAt_pomegaOdd hSC hp hp2 hpc hpdvd q.card_def hd
  | C n q =>
    change p ≠ (TauCeti.LieTypeIndex.C n q).characteristic at hpc
    rw [TauCeti.LieTypeIndex.characteristic_C] at hpc
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_C n q hd (MulEquiv.refl _)
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.C n q, hd⟩).Group :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      exact outerIdxAt_C hp hp2 hd (MulEquiv.refl _) hpc hpdvd
    · have h2n : 2 ≤ n := hadm.2.2.1
      omega
  | D n q =>
    change p ≠ (TauCeti.LieTypeIndex.D n q).characteristic at hpc
    rw [TauCeti.LieTypeIndex.characteristic_D] at hpc
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D n q hd (MulEquiv.refl _)
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.D n q, hd⟩).Group :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      by_cases h43 : n = 4 ∧ p = 3
      · obtain ⟨rfl, rfl⟩ := h43
        exact outerIdxAt_pomegaPlus_four_three hpc q.card_def hSC hpdvd
      · have hn : 5 ≤ n ∨ 3 < p := by
          have h4n : 4 ≤ n := hSC.1.2.2
          have h2 := hp.two_le
          omega
        exact outerIdxAt_pomegaPlus hSC hn hp hp2 hpc hpdvd q.card_def hd
    · have h4n : 4 ≤ n := hadm.2.2
      omega
  | twistedD n q =>
    change p ≠ (TauCeti.LieTypeIndex.twistedD n q).characteristic at hpc
    rw [TauCeti.LieTypeIndex.characteristic_twistedD] at hpc
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD n q hd (MulEquiv.refl _)
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hd⟩).Group :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      exact outerIdxAt_pomegaMinus hSC hp hp2 hpc hpdvd q.card_def hd
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
