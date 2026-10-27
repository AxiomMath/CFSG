module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusUniqueBoundsAut
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusUniqueBoundsCases
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Unique
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsLagrangian
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Graph

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
  (finite_mulAut_matrixProjectiveDerived)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed)
open CFSG.Open (ordD ordTwistedD)

section Linear

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem not_dvd_two_mul_card_mulAut_minus_of_isometry {n : ℕ} (hn : 5 ≤ n)
    (hFK : Nat.card F = Nat.card K ^ 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (s : matrixIsometries (coordinateQuadPlus n F)) (hss : s * s = 1) :
    ¬ Nat.card (fixedSubgroup (matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s))) ∣
      2 * Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) := by
  intro hdvd
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hF : Nat.card F = 2 ^ (2 * f) := by rw [hFK, hK, ← pow_mul, mul_comm]
  have := finite_mulAut_matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)
  have hAut := factorization_two_card_mulAut_coordinateMinus hf hK (by omega : 4 ≤ n) hirr
  have h2A := factorization_two_two_mul_le
    (Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))))
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
  · have hreg := regular_coordinateQuadPlus n F (by omega)
    have hE := commutator_coordinateQuadPlus n F (by omega)
    have hlin := omegaLinearInvolutionTwoPart_of_lagrangian hn hF hreg.1 hreg.2 hE
      (omegaLagrangianInvolutionTwoPart_holds hn hF hreg.1 hE)
    have h := hlin s hss hs1
    have e1 : 2 * f * (n * (n - 1) + 4) = 2 * (f * (n * (n - 1)) + 4 * f) := by ring
    omega

end Linear

section Main

theorem mul_mul_inv_trans_eq_congr {X Y : Type*} [Group X] [Group Y] (E : X ≃* Y) (Θ : Y ≃* X)
    (B : MulAut X) :
    (E.trans Θ : MulAut X) * B * (E.trans Θ : MulAut X)⁻¹ = MulAut.congr Θ (MulAut.congr E B) :=
  MulEquiv.ext fun _ => rfl

theorem omegaMinusInvolutionCentralizerInput_holds {n : ℕ} (hn5 : 5 ≤ n) :
    OmegaMinusInvolutionCentralizerInput n := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  intro hn K F _ _ _ _ _ _ σ hσ hFK b c hirr β γ hβ hγ hirrF B hBB hB hdvd
  obtain ⟨α, hα, -, hβ0⟩ := exists_root_frob_of_irreducible hσ hβ hγ hirrF
  have hαα : α ≠ -β - α := root_ne_other_of_ne_zero hβ0
  set E := minusPlusProjEquiv (r := r) (by omega) hα hαα with hEdef
  set Y := MulAut.congr E B with hY
  have hYY : Y * Y = 1 := by rw [hY, ← map_mul, hBB, map_one]
  have hCY : Nat.card (fixedSubgroup Y) = Nat.card (fixedSubgroup B) := by
    rw [hY, CFSG.ComponentClassification.ExcSelector.fixedSubgroup_congr,
      Subgroup.card_map_of_injective E.injective]
  obtain ⟨f, hf, hKf⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hF : Nat.card F = 2 ^ (2 * f) := by rw [hFK, hKf, ← pow_mul, mul_comm]
  rcases involution_cases_omegaPlus_minusForm (by omega : 5 ≤ r + 1) hσ hβ hγ hirrF hYY with
    ⟨s, hss, hsY⟩ | ⟨g, hg, hFg, hdg⟩ | ⟨Θ, hΘ⟩
  ·
    apply not_dvd_two_mul_card_mulAut_minus_of_isometry (by omega) hFK hirr s hss
    rw [hsY, hCY]
    exact hdvd
  ·
    have hgf : g = f := by
      have h1 : 2 * g = 2 * f := Nat.pow_right_injective (le_refl 2) (hFg.symm.trans hF)
      omega
    subst hgf
    have h1 : ordD (r + 1) (2 ^ g) ∣ 4 * g * ordTwistedD (r + 1) (2 ^ g) := by
      refine hdg.trans ?_
      rw [hCY]
      refine hdvd.trans ?_
      have h2 := card_mulAut_coordinateMinus_dvd hf hKf (by omega : 4 ≤ r + 1) hirr
      have e : 4 * g * ordTwistedD (r + 1) (2 ^ g) = 2 * (2 * g * ordTwistedD (r + 1) (2 ^ g)) := by
        ring
      rw [e]
      exact Nat.mul_dvd_mul_left 2 h2
    exact not_ordD_dvd_mul_ordTwistedD hg (by omega) h1
  ·
    apply hB (E.trans Θ)
    rw [mul_mul_inv_trans_eq_congr, ← hY]
    exact hΘ

end Main

end CFSG.SeitzReduction.OmegaPilot
