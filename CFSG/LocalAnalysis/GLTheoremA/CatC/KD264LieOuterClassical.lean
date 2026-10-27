module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterOrthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterD4Three

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.RankThree.PartOne FOC CFSG.RankThree.PartOne.KCOrthogonalD4
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem outerPLayerAt_D
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} {q : TauCeti.PrimePower}
    {S : Type} [Group S] [Finite S]
    (h : CFSG.Open.StatedClassicalModel S .POmegaPlus n q.p q.exponent)
    (hpq : p ≠ q.p) (hpdvd : p ∣ Nat.card S) : OuterPLayerAt p S := by
  by_cases h43 : n = 4 ∧ p = 3
  · obtain ⟨rfl, hp3⟩ := h43
    subst hp3
    exact outerPLayerAt_pomegaPlus_four_three hpq h hpdvd
  · have hn4 : 4 ≤ n := h.1.2.2
    have hn : 5 ≤ n ∨ 3 < p := by
      have h2 := hp.two_le
      omega
    exact outerPLayerAt_pomegaPlus h hn hp hp2 hpq hpdvd

theorem outerPLayerAt_twistedD {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} {q : TauCeti.PrimePower} {S : Type} [Group S] [Finite S]
    (h : CFSG.Open.StatedClassicalModel S .POmegaMinus n q.p q.exponent)
    (hpq : p ≠ q.p) (hpdvd : p ∣ Nat.card S) : OuterPLayerAt p S := by
  have h' := h
  obtain ⟨-, K, hfield, hfinite, hK, b, c, hirr, ⟨eK⟩⟩ := h
  have hn4 : 4 ≤ n := h'.1.2.2
  have hn : 1 ≤ n := by omega
  exact outerPLayerAt_pomegaMinus hn h' hp hp2 hpq hK b c hirr eK hpdvd

theorem lieOuterPLayer_classicalBCD
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : LieOuterPLayer p isClassicalBCDIdx := by
  intro d hd hP hnExc S hS hfin e hnot hpdvd
  obtain ⟨e⟩ := e
  cases d with
  | B n q =>
    have hpq : q.p ≠ p := by
      have h := characteristic_ne_of_not_isChevSimple hd ⟨e⟩ hnot
      rwa [TauCeti.LieTypeIndex.characteristic_B] at h
    rcases CFSG.Models.lieModel_B n q hd e with hB | hB
    · exact outerPLayerAt_of_lieModel_B_PSp hp hp2 hB hpq hpdvd
    · have hn3 : 3 ≤ n := hB.1.2.2.1
      rcases hB.2 with hSC | ⟨h0, -⟩
      · exact outerPLayerAt_pomegaOdd hSC hp hp2 hpq.symm hpdvd
      · omega
  | C n q =>
    exact outerPLayerAt_C hp hp2 hd e hnot hpdvd
  | D n q =>
    have hpq : q.p ≠ p := by
      have h := characteristic_ne_of_not_isChevSimple hd ⟨e⟩ hnot
      rwa [TauCeti.LieTypeIndex.characteristic_D] at h
    have hSC : CFSG.Open.StatedClassicalModel S .POmegaPlus n q.p q.exponent := by
      rcases (CFSG.Models.lieModel_D n q hd e).2 with h | ⟨h0, -⟩
      · exact h
      · have hn4 : 4 ≤ n := (CFSG.Models.lieModel_D n q hd e).1.2.2
        omega
    exact outerPLayerAt_D hp hp2 hSC hpq.symm hpdvd
  | twistedD n q =>
    have hpq : q.p ≠ p := by
      have h := characteristic_ne_of_not_isChevSimple hd ⟨e⟩ hnot
      rwa [TauCeti.LieTypeIndex.characteristic_twistedD] at h
    have hSC : CFSG.Open.StatedClassicalModel S .POmegaMinus n q.p q.exponent := by
      rcases (CFSG.Models.lieModel_twistedD n q hd e).2 with h | ⟨h0, -⟩
      · exact h
      · have hn4 : 4 ≤ n := (CFSG.Models.lieModel_twistedD n q hd e).1.2.2
        omega
    exact outerPLayerAt_twistedD hp hp2 hSC hpq.symm hpdvd
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
