module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Reps
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Diag
public import CFSG.RankThree.Lattice.SteinbergBIRoots

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.ComponentClassification.Burgoyne.E2 CFSG.RankThree.Lattice

@[expose] def regFamD : List ((Fin Tag.E6.rank → ℤ) × ℤ) :=
  [(![0, 0, 0, 0, 0, 1], -5), (![0, 0, 0, 0, 1, 0], 1), (![0, 0, 0, 1, 0, 0], -2),
    (![1, 1, 1, 1, 0, 0], -1)]

@[expose] def regFamA : List ((Fin Tag.E6.rank → ℤ) × ℤ) :=
  [(![0, 0, 0, 0, 0, 1], -3), (![0, 0, 0, 0, 1, 0], 2), (![0, 0, 1, 0, 0, 0], -1),
    (![0, 1, 0, 0, 0, 0], -3), (![1, 1, 2, 3, 2, 1], 2)]

@[expose] def regZD : Fin Tag.E6.rank → ℤ := ![-1, 1, 2, -5, 10, -11]

@[expose] def regZA : Fin Tag.E6.rank → ℤ := ![1, -8, -2, 4, 7, -8]

theorem regCoweight_regFamD : ∀ j, regCoweight regFamD j = regZD j := by
  decide +kernel

theorem regCoweight_regFamA : ∀ j, regCoweight regFamA j = regZA j := by
  decide +kernel

theorem regFamD_mem :
    ∀ y ∈ regFamD, IsRoot Tag.E6 y.1 ∧ triPairing repD y.1 = 0 := by
  have h : ∀ y ∈ regFamD, List.ofFn y.1 ∈ Tag.E6.artifactRoots ∧ triPairing repD y.1 = 0 := by
    decide +kernel
  exact fun y hy => ⟨isRoot_iff_mem_artifactRoots.2 (h y hy).1, (h y hy).2⟩

theorem regFamA_mem :
    ∀ y ∈ regFamA, IsRoot Tag.E6 y.1 ∧ triPairing repA y.1 = 0 := by
  have h : ∀ y ∈ regFamA, List.ofFn y.1 ∈ Tag.E6.artifactRoots ∧ triPairing repA y.1 = 0 := by
    decide +kernel
  exact fun y hy => ⟨isRoot_iff_mem_artifactRoots.2 (h y hy).1, (h y hy).2⟩

theorem regZD_pairing :
    ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      (∑ j, regZD j * α j) ≠ 0 ∧ (∑ j, regZD j * α j).natAbs < 12 := by
  rw [forall_isRoot_iff]
  decide +kernel

theorem regZA_pairing :
    ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      (∑ j, regZA j * α j) ≠ 0 ∧ (∑ j, regZA j * α j).natAbs < 12 := by
  rw [forall_isRoot_iff]
  decide +kernel

theorem exists_regFam {b : Fin Tag.E6.rank → ZMod 3}
    (hb : b = repD ∨ b = repA) :
    ∃ Γ : List ((Fin Tag.E6.rank → ℤ) × ℤ),
      (∀ y ∈ Γ, IsRoot Tag.E6 y.1 ∧ triPairing b y.1 = 0) ∧
      ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
        (∑ j, regCoweight Γ j * α j) ≠ 0 ∧ (∑ j, regCoweight Γ j * α j).natAbs < 12 := by
  rcases hb with rfl | rfl
  · refine ⟨regFamD, regFamD_mem, fun α hα => ?_⟩
    simp only [regCoweight_regFamD]
    exact regZD_pairing α hα
  · refine ⟨regFamA, regFamA_mem, fun α hα => ?_⟩
    simp only [regCoweight_regFamA]
    exact regZA_pairing α hα

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
