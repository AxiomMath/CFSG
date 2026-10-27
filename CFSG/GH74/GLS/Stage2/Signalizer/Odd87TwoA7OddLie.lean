module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BLin
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BUni
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BSym
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BG2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BD4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerGraphHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerPSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTrialityInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

theorem ne_two_of_pow_mod_four' {p f : ℕ} (hf : 1 ≤ f) (h : p ^ f % 4 = 3 ∨ p ^ f % 4 = 1) :
    p ≠ 2 := by
  rintro rfl
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rcases g with _ | g
  · simp at h
  · have : 2 ^ (g + 1 + 1) = 4 * 2 ^ g := by ring
    rw [this] at h
    omega

theorem admissible_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (_ht : t ≠ .twistedB2) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem noTwoA7ClassicalAt_of_family {X : Type} [Group X] [Finite X] {τ : StatedLieTag}
    {n p f : ℕ} (hO : LieOrderFormulasInput) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible τ n p f)
    (hm : LieModel X τ n p f) (hG : GLS3OddFamilyInput τ) (hZ : Subgroup.center X = ⊥) {z : X}
    (hB : orderOf z = 2 → BTwo X z) : NoTwoA7ClassicalAt z := by
  intro hz
  have hα := orderOf_conj_eq_two hZ hz
  refine noTwoA7ClassicalAt_of_data hO hp2 (hB hz) (fun S hS => ?_) hz
  rcases hG X n p f hadm.1 hp2 hadm hm (MulAut.conj z) hα S hS with h | ⟨-, -, hout, -⟩
  · exact h
  · exact absurd ⟨z, rfl⟩ hout

section Cells

theorem twoA7OddLie : TwoA7OddLie := by
  have hO : LieOrderFormulasInput := lieOrderFormulasInput
  intro X _ _ hZ hOdd z
  obtain ⟨p, f, hp, hf, h⟩ := hOdd
  rcases h with ⟨hp2, h⟩ | ⟨hp2, -, hm⟩ | ⟨hp2, -, hm⟩ | ⟨h3, hm⟩ | ⟨h1, hm⟩ | hm
  · rcases h with hm | hm | hm | hm | hm | hm
    · have hadm := admissible_of_lieModel hm (by decide)
      exact noTwoA7ClassicalAt_of_family hO hp2 hadm hm gls3OddFamilyInput_PSL_holds hZ
        (fun hz => bTwo_psl hp hp2 hadm hm hZ hz)
    · have hadm := admissible_of_lieModel hm (by decide)
      exact noTwoA7ClassicalAt_of_family hO hp2 hadm hm gls3OddFamilyInput_PSL_holds hZ
        (fun hz => bTwo_psl hp hp2 hadm hm hZ hz)
    · have hadm := admissible_of_lieModel hm (by decide)
      exact noTwoA7ClassicalAt_of_family hO hp2 hadm hm gls3OddFamilyInput_PSU_holds hZ
        (fun hz => bTwo_psu hp hp2 hadm hm hZ hz)
    · have hadm := admissible_of_lieModel hm (by decide)
      exact noTwoA7ClassicalAt_of_family hO hp2 hadm hm gls3OddFamilyInput_PSp_holds hZ
        (fun hz => bTwo_psp hp hp2 hadm hm hZ hz)
    · have hadm := admissible_of_lieModel hm (by decide)
      exact noTwoA7ClassicalAt_of_family hO hp2 hadm hm
        (gls3OddFamilyInput_G2 oddExcInnerDiagInput_G2) hZ (fun hz => bTwo_g2 hp hp2 hadm hm hZ hz)
    · have hadm := admissible_of_lieModel hm (by decide)
      exact noTwoA7ClassicalAt_of_family hO hp2 hadm hm
        (gls3OddFamilyInput_trialityD4 oddTrialityInnerInput_holds oddTrialityOuterInput_holds)
        hZ (fun hz => bTwo_d4 hp hp2 hadm hm hZ hz)
  · have hadm := admissible_of_lieModel hm (by decide)
    exact noTwoA7ClassicalAt_of_family hO hp2 hadm hm gls3OddFamilyInput_PSL_holds hZ
      (fun hz => bTwo_psl hp hp2 hadm hm hZ hz)
  · have hadm := admissible_of_lieModel hm (by decide)
    exact noTwoA7ClassicalAt_of_family hO hp2 hadm hm gls3OddFamilyInput_PSU_holds hZ
      (fun hz => bTwo_psu hp hp2 hadm hm hZ hz)
  · have hp2 : p ≠ 2 := ne_two_of_pow_mod_four' hf (Or.inl h3)
    have hadm := admissible_of_lieModel hm (by decide)
    exact noTwoA7ClassicalAt_of_family hO hp2 hadm hm gls3OddFamilyInput_PSL_holds hZ
      (fun hz => bTwo_psl hp hp2 hadm hm hZ hz)
  · have hp2 : p ≠ 2 := ne_two_of_pow_mod_four' hf (Or.inr h1)
    have hadm := admissible_of_lieModel hm (by decide)
    exact noTwoA7ClassicalAt_of_family hO hp2 hadm hm gls3OddFamilyInput_PSU_holds hZ
      (fun hz => bTwo_psu hp hp2 hadm hm hZ hz)
  · have hadm := admissible_of_lieModel hm (by decide)
    exact noTwoA7ClassicalAt_of_family hO (by norm_num) hadm hm
      (gls3OddFamilyInput_twistedG2 oddReeInnerInput_holds) hZ
      (fun hz => bTwo_ree Nat.prime_three (by norm_num) hadm hm hZ hz)

end Cells

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
