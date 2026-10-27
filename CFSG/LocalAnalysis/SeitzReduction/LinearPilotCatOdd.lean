module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatOdd

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def SLmNotOddLieInputAt (m : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), (m, f) ≠ (3, 1) → LieModel X .PSL m 2 f → ¬ OddLieType X

@[expose] def SLmNotOddLieInput : Prop :=
  ∀ m : ℕ, 3 ≤ m → SLmNotOddLieInputAt m

theorem eq_three_one_of_two_pow_dvd {m f N : ℕ} (hm : 3 ≤ m) (hf : 1 ≤ f)
    (hdvd : 2 ^ (f * ((m - 1) * (m - 1 + 1) / 2)) ∣ N) (h16 : ¬ 16 ∣ N) : m = 3 ∧ f = 1 := by
  set M := f * ((m - 1) * (m - 1 + 1) / 2) with hM
  have hM3 : M ≤ 3 := by
    by_contra h
    exact h16 ((Nat.pow_dvd_pow 2 (by omega : 4 ≤ M)).trans hdvd)
  have hT3 : 3 ≤ (m - 1) * (m - 1 + 1) / 2 := by
    have : 2 * 3 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hTM : (m - 1) * (m - 1 + 1) / 2 ≤ M := Nat.le_mul_of_pos_left _ hf
  have hf1 : f = 1 := by
    by_contra h
    have : 2 * 3 ≤ f * ((m - 1) * (m - 1 + 1) / 2) := Nat.mul_le_mul (by omega) hT3
    omega
  have hm3 : m = 3 := by
    by_contra h
    have : 3 * 4 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  exact ⟨hm3, hf1⟩

theorem catSLmOddLieAt_of_inputs (hGLS : GLS3OddLieAutComponentsInput) {m : ℕ} (hm : 3 ≤ m)
    (hX : SLmNotOddLieInputAt m) : CatSLmOddLieAt m := by
  intro S _ _ _ _ hodd σ hσ f D hD hDm
  have hf : 1 ≤ f :=
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hDm).1.2.1
  obtain ⟨t, n, p, e, hp, hp2, hadm, hmS⟩ := hodd
  rcases hGLS S t n p e hp hp2 hadm hmS σ hσ D hD with ⟨τ', n', f', hadm', hm'⟩ | ⟨-, -, -, hL⟩
  · by_contra hne
    exact hX (D ⧸ center D) f
      (fun h => hne ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩) hDm
      ⟨τ', n', p, f', hp, hp2, hadm', hm'⟩
  · have h504 := F4Pilot.card_of_lieModel_PSL_two_two_three hL
    have hdvd' : Nat.card (D ⧸ center D) ∣ 504 := h504 ▸ card_quotient_dvd_card _
    rw [card_of_lieModel_PSL_two hDm] at hdvd'
    obtain ⟨hdvd, -, -⟩ := ordA_two_pow_bounds (by omega : 1 ≤ m - 1) hf
    exact eq_three_one_of_two_pow_dvd hm hf (hdvd.trans hdvd') (by decide)

theorem catSLmOddLie_of_inputs (hGLS : GLS3OddLieAutComponentsInput) (hX : SLmNotOddLieInput) :
    CatSLmOddLie :=
  fun m hm => catSLmOddLieAt_of_inputs hGLS hm (hX m hm)

end CFSG.SeitzReduction.LinearPilot
