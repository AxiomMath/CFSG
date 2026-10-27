module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaInvolutionConjugacy
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsAut

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

section Exclusion

@[expose] def OmegaInvolutionBoundsDvd (P : Type*) [Group P] (n f : ℕ) : Prop :=
  ∀ θ : MulAut P, θ * θ = 1 → θ ≠ 1 →
    f * (n * (n - 1) + 4) ≤ 2 * (Nat.card (fixedSubgroup θ)).factorization 2 ∨
    ∃ g : ℕ, f = 2 * g ∧ (ordD n (2 ^ g) ∣ Nat.card (perfectCore (fixedSubgroup θ)) ∨
      ordTwistedD n (2 ^ g) ∣ Nat.card (perfectCore (fixedSubgroup θ)))

theorem factorization_two_le_of_dvd_ne_zero {A B : ℕ} (h : A ∣ B) (hB : B ≠ 0) :
    A.factorization 2 ≤ B.factorization 2 :=
  (Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hB h) hB).2 h 2

theorem le_factorization_two_fixedSubgroup {P : Type*} [Group P] [Finite P] {n g : ℕ}
    (hn : 1 ≤ n) (hg : 1 ≤ g) (θ : MulAut P)
    (hd : ordD n (2 ^ g) ∣ Nat.card (perfectCore (fixedSubgroup θ)) ∨
      ordTwistedD n (2 ^ g) ∣ Nat.card (perfectCore (fixedSubgroup θ))) :
    g * (n * (n - 1)) ≤ (Nat.card (fixedSubgroup θ)).factorization 2 := by
  have hPC : Nat.card (perfectCore (fixedSubgroup θ)) ∣ Nat.card (fixedSubgroup θ) :=
    Subgroup.card_dvd_of_le (perfectCore_le _)
  rcases hd with hd | hd
  · rw [← factorization_two_ordD hg hn]
    exact factorization_two_le_of_dvd_ne_zero (hd.trans hPC) Nat.card_pos.ne'
  · rw [← factorization_two_ordTwistedD hg hn]
    exact factorization_two_le_of_dvd_ne_zero (hd.trans hPC) Nat.card_pos.ne'

theorem swapPairExclusion_of_involutionBoundsDvd {P : Type*} [Group P] [Finite P] {n f : ℕ}
    (hn : 4 ≤ n) (hf : 2 ≤ f)
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

end Exclusion

section Linear

@[expose] def OmegaLinearInvolutionTwoPart {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (n f : ℕ) : Prop :=
  ∀ s : matrixIsometries Q, s * s = 1 → s ≠ 1 →
    f * (n * (n - 1) + 4) ≤ 2 * (Nat.card (fixedSubgroup
      (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)))).factorization 2

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem omegaInvolutionBoundsDvd_of_linear (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (htop : matrixProjectiveImage Q = ⊤)
    (hI : OmegaLinearInvolutionTwoPart Q n f) :
    OmegaInvolutionBoundsDvd (matrixProjectiveDerived Q) n f := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  intro θ hθθ hθ1
  have hθ2 : orderOf θ = 2 := orderOf_eq_prime (by rw [sq]; exact hθθ) hθ1
  have hα : θ ∈ matrixProjectiveImage Q := htop ▸ Subgroup.mem_top θ
  obtain ⟨S, hS, hSθ⟩ := exists_unit_rep hα
  by_cases hσ : S.val.right = 1
  · obtain ⟨-, -, -, -, F, hF, hker, hinjκ, -⟩ :=
      evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
    have hmem : (⟨matrixProjectiveConjugationHom Q S, ⟨S, rfl⟩⟩ : matrixProjectiveImage Q) ∈
        F.ker := by
      rw [MonoidHom.mem_ker, hF, hσ]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) = θ := hs.trans hSθ
    have hss : s * s = 1 := by
      apply hinjκ
      rw [map_mul, map_one, MonoidHom.comp_apply, hs', hθθ]
    have hs1 : s ≠ 1 := by
      rintro rfl
      apply hθ1
      rw [← hs', map_one, map_one]
    have h := hI s hss hs1
    rw [hs'] at h
    exact Or.inl h
  · obtain ⟨g, hfg, hd⟩ :=
      exists_dvd_card_perfectCore_fixedSubgroup_of_field hf hK hn hQ hT hE hα hθ2 hS hSθ hσ
    exact Or.inr ⟨g, hfg, hd⟩

theorem swapPairExclusion_coordinatePlus_of_linear (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n) (hI : OmegaLinearInvolutionTwoPart (coordinateQuadPlus n K) n f) :
    SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hreg := regular_coordinateQuadPlus n K (by omega)
  have htop : matrixProjectiveImage (coordinateQuadPlus n K) = ⊤ :=
    (OmegaRadical.semilinearImageEqTop _ .POmegaPlus (Or.inl rfl)
      (statedClassicalModel_coordinatePlus (by omega) hK (by omega))) hn K hK
      (coordinatePlusWitnessEquiv K (MulEquiv.refl _)).symm
  exact swapPairExclusion_of_involutionBoundsDvd (by omega) hf
    (Or.inl (card_coordinatePlus (by omega) hK (by omega)))
    (factorization_two_card_mulAut_coordinatePlus (by omega) hK hn)
    (omegaInvolutionBoundsDvd_of_linear (by omega) hK (by omega) hreg.1 hreg.2
      (commutator_coordinateQuadPlus n K (by omega)) htop hI)

theorem swapPairExclusion_coordinateMinus_of_linear (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (h1 : 1 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hI : OmegaLinearInvolutionTwoPart (coordinateQuadMinus n K h1 b c) n f) :
    SwapPairExclusion (matrixProjectiveDerived (coordinateQuadMinus n K h1 b c)) := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  have htop : matrixProjectiveImage (coordinateQuadMinus n K h1 b c) = ⊤ :=
    (OmegaRadical.semilinearImageEqTop _ .POmegaMinus (Or.inr rfl)
      (statedClassicalModel_coordinateMinus (by omega) hK hn h1 hirr)) h1 K hK b c hirr
      (coordinateMinusWitnessEquiv K h1 b c (MulEquiv.refl _)).symm
  exact swapPairExclusion_of_involutionBoundsDvd hn hf
    (Or.inr (card_coordinateMinus (by omega) hK hn h1 hirr))
    (factorization_two_card_mulAut_coordinateMinus (by omega) hK hn hirr)
    (omegaInvolutionBoundsDvd_of_linear (by omega) hK hn hreg.1 hreg.2
      (commutator_coordinateQuadMinus n K b c hn hirr) htop hI)

end Linear

end CFSG.SeitzReduction.OmegaPilot
