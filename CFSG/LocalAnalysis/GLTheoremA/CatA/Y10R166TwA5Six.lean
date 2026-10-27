module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotWeakCTNormal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 f F)

@[expose] def suFiveIndex : Finset (Fin 6) := Finset.univ.erase 5

theorem card_suFiveIndex : suFiveIndex.card = 5 := by
  simp [suFiveIndex]

theorem compl_suFiveIndex : suFiveIndexᶜ = {5} := by
  ext i
  simp [suFiveIndex, eq_comm]

theorem six_two_pow_ne_three_two {f : ℕ} (hf : 2 ≤ f) : (6, 2 ^ f) ≠ (3, 2) := by
  intro hc
  have h2 : 2 ^ f = 2 := (Prod.ext_iff.1 hc).2
  have h1 : f = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using h2)
  omega

theorem center_unitaryPSU_six (hf : 2 ≤ f) :
    Subgroup.center (unitaryPSU h 6) = ⊥ :=
  center_unitaryPSU_eq_bot h (by norm_num) (six_two_pow_ne_three_two hf)

theorem isQuasisimple_unitaryPSU_six (hf : 2 ≤ f) :
    CFSG.IsQuasisimple (unitaryPSU h 6) :=
  isQuasisimple_unitaryPSU h (by norm_num) (six_two_pow_ne_three_two hf)

theorem hasLabel_unitaryPSU_six (hf : 2 ≤ f) :
    HasLabel (unitaryPSU h 6) (· = (⟨.twA, 5, f⟩ : GLALabel)) := by
  have hne := six_two_pow_ne_three_two hf
  refine hasLabel_of_statedClassicalModel_PSU (r := 5) (n := f)
    (isQuasisimple_unitaryPSU_six h hf) ?_
  have hStated : StatedClassicalModel (unitaryPSU h 6) .PSU 6 2 f := by
    refine ⟨⟨Nat.prime_two, h.one_le, by norm_num, hne⟩, ?_⟩
    exact ⟨F, inferInstance, inferInstance,
      by rw [h.card, show 2 * f = f * 2 by omega, pow_mul],
      ⟨unitaryPSUEquiv h (by norm_num)⟩⟩
  have hiso : unitaryPSU h 6 ⧸ Subgroup.center (unitaryPSU h 6) ≃* unitaryPSU h 6 :=
    (QuotientGroup.quotientMulEquivOfEq (center_unitaryPSU_six h hf)).trans
      QuotientGroup.quotientBot
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv hiso.symm hStated

end CFSG.LocalAnalysis.GLTheoremA.Y10F
