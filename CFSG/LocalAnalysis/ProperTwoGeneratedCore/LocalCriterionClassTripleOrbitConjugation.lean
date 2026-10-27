module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransportAction

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbit

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

theorem rightAct_rightConjugateElem (x : Ω) (z a : G) :
    rightAct (rightAct x a) (rightConjugateElem z a) =
      rightAct (rightAct x z) a := by
  rw [rightAct_mul, rightAct_mul]
  simp only [rightConjugateElem, mul_assoc, mul_inv_cancel_left]

theorem unique_fixed_point_rightConjugateElem {z : G} {alpha : Ω}
    (hunique : ∀ x : Ω, rightAct x z = x ↔ x = alpha) (a : G) (gamma : Ω) :
    rightAct gamma (rightConjugateElem z a) = gamma ↔ gamma = rightAct alpha a := by
  have hcancel : rightAct (rightAct gamma a⁻¹) a = gamma := by
    rw [rightAct_mul, inv_mul_cancel, rightAct_one]
  constructor
  · intro hgamma
    have hfixed : rightAct (rightAct gamma a⁻¹) z = rightAct gamma a⁻¹ := by
      apply rightAct_injective a
      change rightAct (rightAct (rightAct gamma a⁻¹) z) a =
        rightAct (rightAct gamma a⁻¹) a
      rw [← rightAct_rightConjugateElem (rightAct gamma a⁻¹) z a, hcancel, hgamma]
    have hbase := (hunique _).mp hfixed
    calc
      gamma = rightAct (rightAct gamma a⁻¹) a := hcancel.symm
      _ = rightAct alpha a := congrArg (fun x : Ω => rightAct x a) hbase
  · intro hgamma
    rw [hgamma, rightAct_rightConjugateElem, (hunique alpha).mpr rfl]

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbit
