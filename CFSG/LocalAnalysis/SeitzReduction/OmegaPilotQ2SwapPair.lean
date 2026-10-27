module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsLagrangian

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.ClassicalGroups.Orthogonal
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (ordD ordTwistedD)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)

theorem swapPairExclusion_of_involutionBoundsDvd_of_one_le {P : Type*} [Group P] [Finite P]
    {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hP : Nat.card P = ordD n (2 ^ f) ∨ Nat.card P = ordTwistedD n (2 ^ f))
    (hAut : (Nat.card (MulAut P)).factorization 2 ≤ f * (n * (n - 1)) + 1 + f.factorization 2)
    (hB : OmegaInvolutionBoundsDvd P n f) : SwapPairExclusion P := by
  intro θ θ' h1 h2 h3 h4 hC1 hC3
  have h2A := factorization_two_two_mul_le (Nat.card (MulAut P))
  have hvf : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have e1 : f * (n * (n - 1) + 4) = f * (n * (n - 1)) + 4 * f := by ring
  rcases hB θ h1 h2 with hb | ⟨g, hfg, hg3⟩ <;>
    rcases hB θ' h3 h4 with hb' | ⟨g', hfg', hg3'⟩
  · omega
  · have hg2' := le_factorization_two_fixedSubgroup (by omega) (by omega) θ' hg3'
    have e2 : 2 * (g' * (n * (n - 1))) = f * (n * (n - 1)) := by rw [hfg']; ring
    omega
  · have hg2 := le_factorization_two_fixedSubgroup (by omega) (by omega) θ hg3
    have e2 : 2 * (g * (n * (n - 1))) = f * (n * (n - 1)) := by rw [hfg]; ring
    omega
  · have hgg : g' = g := by omega
    rw [hgg] at hg3'
    obtain ⟨A, hA, hAd⟩ : ∃ A, (A = ordD n (2 ^ g) ∨ A = ordTwistedD n (2 ^ g)) ∧
        A ∣ Nat.card (perfectCore (fixedSubgroup θ)) := by
      rcases hg3 with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    obtain ⟨B, hB', hBd⟩ : ∃ B, (B = ordD n (2 ^ g) ∨ B = ordTwistedD n (2 ^ g)) ∧
        B ∣ Nat.card (perfectCore (fixedSubgroup θ')) := by
      rcases hg3' with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    have hC := (mul_dvd_mul hAd hBd).trans hC3
    rw [hfg] at hP
    rcases hP with h | h
    · rw [h] at hC
      exact not_mul_dvd_ord_sq (by omega) hn hA hB' (Or.inl rfl) hC
    · rw [h] at hC
      exact not_mul_dvd_ord_sq (by omega) hn hA hB' (Or.inr rfl) hC

section Coordinate

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem one_le_of_card_eq_two_pow' (hK : Nat.card K = 2 ^ f) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with rfl | h
  · have := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at this
    omega
  · exact h

theorem swapPairExclusion_coordinatePlus_of_one_le (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) :
    SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hf : 1 ≤ f := one_le_of_card_eq_two_pow' hK
  have hreg := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  have htop : matrixProjectiveImage (coordinateQuadPlus n K) = ⊤ :=
    (OmegaRadical.semilinearImageEqTop _ .POmegaPlus (Or.inl rfl)
      (statedClassicalModel_coordinatePlus hf hK (by omega))) hn K hK
      (coordinatePlusWitnessEquiv K (MulEquiv.refl _)).symm
  exact swapPairExclusion_of_involutionBoundsDvd_of_one_le (by omega) hf
    (Or.inl (card_coordinatePlus hf hK (by omega)))
    (factorization_two_card_mulAut_coordinatePlus hf hK hn)
    (omegaInvolutionBoundsDvd_of_linear hf hK (by omega) hreg.1 hreg.2 hE htop
      (omegaLinearInvolutionTwoPart_of_lagrangian hn hK hreg.1 hreg.2 hE
        (omegaLagrangianInvolutionTwoPart_holds hn hK hreg.1 hE)))

theorem swapPairExclusion_coordinateMinus_of_one_le (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (h1 : 1 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    SwapPairExclusion (matrixProjectiveDerived (coordinateQuadMinus n K h1 b c)) := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hf : 1 ≤ f := one_le_of_card_eq_two_pow' hK
  have hreg := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hE := commutator_coordinateQuadMinus n K b c (by omega) hirr
  have htop : matrixProjectiveImage (coordinateQuadMinus n K h1 b c) = ⊤ :=
    (OmegaRadical.semilinearImageEqTop _ .POmegaMinus (Or.inr rfl)
      (statedClassicalModel_coordinateMinus hf hK (by omega) h1 hirr)) h1 K hK b c hirr
      (coordinateMinusWitnessEquiv K h1 b c (MulEquiv.refl _)).symm
  exact swapPairExclusion_of_involutionBoundsDvd_of_one_le (by omega) hf
    (Or.inr (card_coordinateMinus hf hK (by omega) h1 hirr))
    (factorization_two_card_mulAut_coordinateMinus hf hK (by omega) hirr)
    (omegaInvolutionBoundsDvd_of_linear hf hK (by omega) hreg.1 hreg.2 hE htop
      (omegaLinearInvolutionTwoPart_of_lagrangian hn hK hreg.1 hreg.2 hE
        (omegaLagrangianInvolutionTwoPart_holds hn hK hreg.1 hE)))

theorem swapPairExclusion_coordinatePlus_two (hK : Nat.card K = 2) (hn : 5 ≤ n) :
    SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  swapPairExclusion_coordinatePlus_of_one_le (f := 1) (by rw [hK, pow_one]) hn

theorem swapPairExclusion_coordinateMinus_two (hK : Nat.card K = 2) (hn : 5 ≤ n) (h1 : 1 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    SwapPairExclusion (matrixProjectiveDerived (coordinateQuadMinus n K h1 b c)) :=
  swapPairExclusion_coordinateMinus_of_one_le (f := 1) (by rw [hK, pow_one]) hn h1 hirr

end Coordinate

end CFSG.SeitzReduction.OmegaPilot
