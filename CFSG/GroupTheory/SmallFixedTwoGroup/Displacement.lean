module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.CenterQuot

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.Co3Std.CentT (centerQuotAut centerQuotAut_mul centerQuotAut_one
  centerQuotAut_injective card_fixed_centerQuotAut_dvd)

theorem displacement_of_isQuasisimple {E : Type} [Group E] [Finite E] (hE : CFSG.IsQuasisimple E)
    {σ : MulAut E} (hσ : orderOf σ = 2) :
    centerQuotAut σ * centerQuotAut σ = 1 ∧ centerQuotAut σ ≠ 1 ∧
      Nat.card (fixedSubgroup (centerQuotAut σ)) ∣ Nat.card (fixedSubgroup σ) := by
  have hσ2 : σ * σ = 1 := by
    rw [← pow_two, ← hσ]
    exact pow_orderOf_eq_one σ
  have hsq : centerQuotAut σ * centerQuotAut σ = 1 := by
    rw [← centerQuotAut_mul, hσ2, centerQuotAut_one]
  have hne : centerQuotAut σ ≠ 1 := by
    intro h
    have hσeq1 : σ = 1 :=
      centerQuotAut_injective hE.1.commutator_eq_top (h.trans centerQuotAut_one.symm)
    have h1 : orderOf (1 : MulAut E) = 2 := by
      rw [← hσeq1]
      exact hσ
    rw [orderOf_one] at h1
    omega
  exact ⟨hsq, hne, card_fixed_centerQuotAut_dvd σ⟩

end CFSG.GroupTheory.SmallFixedTwoGroup
