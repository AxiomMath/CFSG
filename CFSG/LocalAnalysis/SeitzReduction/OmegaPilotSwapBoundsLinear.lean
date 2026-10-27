module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBounds
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueLinear

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
  (finite_mulAut_matrixProjectiveDerived)

theorem fixedSubgroup_one_eq_top {P : Type*} [Group P] : fixedSubgroup (1 : MulAut P) = ⊤ := by
  ext x
  simp only [Subgroup.mem_top, iff_true]
  rfl

theorem omegaPlusLinearInvolutionInput_of_linear {n : ℕ} (hn : 5 ≤ n)
    (hI : ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (e : ℕ), Nat.card F = 2 ^ e →
      OmegaLinearInvolutionTwoPart (coordinateQuadPlus n F) n e) :
    OmegaPlusLinearInvolutionInput n := by
  intro K F _ _ _ _ _ _ hFK s hss hdvd
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hF : Nat.card F = 2 ^ (2 * f) := by rw [hFK, hK, ← pow_mul, mul_comm]
  have := finite_mulAut_matrixProjectiveDerived (coordinateQuadPlus n K)
  have hAut := factorization_two_card_mulAut_coordinatePlus hf hK hn
  have h2A := factorization_two_two_mul_le
    (Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))))
  have hvf : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hle := factorization_two_le_of_dvd_ne_zero hdvd (mul_ne_zero two_ne_zero Nat.card_pos.ne')
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one, map_one, fixedSubgroup_one_eq_top, Subgroup.card_top,
      card_coordinatePlus (by omega) hF (by omega), factorization_two_ordD (by omega) (by omega)]
      at hle
    have hnn : 20 ≤ n * (n - 1) := by
      have : 4 ≤ n - 1 := by omega
      nlinarith
    nlinarith
  · have h := hI F (2 * f) hF s hss hs1
    have e1 : 2 * f * (n * (n - 1) + 4) = 2 * (f * (n * (n - 1)) + 4 * f) := by ring
    omega

end CFSG.SeitzReduction.OmegaPilot
