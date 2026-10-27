module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurReduction
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightInputs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour
public import CFSG.Walter.Bender1970

public section

namespace CFSG.ComponentClassification.WalterSchur

theorem walter_schur_two_part_holds :
    ∀ (K : Type) [Group K] [Finite K] (Z₀ : Subgroup K) [Z₀.Normal],
      CFSG.Open.IsQuasisimple K → Z₀ ≤ Subgroup.center K → IsPGroup 2 Z₀ →
      ∀ P : Sylow 2 (K ⧸ Z₀), IsMulCommutative (P : Subgroup (K ⧸ Z₀)) →
        Nat.card Z₀ ≤ 2 ∧ (8 ≤ Nat.card P → Z₀ = ⊥) :=
  walter_schur_two_part_of_simpleCaseHyp (Walter.simpleCaseHyp_of_benderHyp Walter.benderHyp)

theorem theorem48Inputs_of_goldschmidt (hG : CFSG.Goldschmidt.TopStatement) :
    AschbacherTheorem3.Theorem48Inputs :=
  ⟨GoldschmidtFour.goldschmidt_theorem_four_holds, walter_schur_two_part_holds, hG⟩

end CFSG.ComponentClassification.WalterSchur
