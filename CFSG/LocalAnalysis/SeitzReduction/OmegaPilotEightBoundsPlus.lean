module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightBounds

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
  (finite_mulAut_matrixProjectiveDerived)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Open (ordD ordTwistedD)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)
open scoped Pointwise

section Conj

variable {P : Type*} [Group P]

theorem fixedSubgroup_inv_mul_mul_eq_map (β θ : MulAut P) :
    fixedSubgroup (β⁻¹ * θ * β) = (fixedSubgroup θ).map (β⁻¹ : MulAut P).toMonoidHom := by
  ext x
  constructor
  · intro hx
    have h : β⁻¹ (θ (β x)) = x := hx
    refine ⟨β x, ?_, ?_⟩
    · change θ (β x) = β x
      have h2 := congrArg β h
      rwa [MulAut.apply_inv_self] at h2
    · change β⁻¹ (β x) = x
      exact MulAut.inv_apply_self P β x
  · rintro ⟨y, hy, rfl⟩
    have hy' : θ y = y := hy
    change β⁻¹ (θ (β (β⁻¹ y))) = β⁻¹ y
    rw [MulAut.apply_inv_self, hy']

theorem card_fixedSubgroup_inv_mul_mul (β θ : MulAut P) :
    Nat.card (fixedSubgroup (β⁻¹ * θ * β)) = Nat.card (fixedSubgroup θ) := by
  rw [fixedSubgroup_inv_mul_mul_eq_map]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

theorem card_perfectCore_fixedSubgroup_inv_mul_mul [Finite P] (β θ : MulAut P) :
    Nat.card (perfectCore (fixedSubgroup (β⁻¹ * θ * β))) =
      Nat.card (perfectCore (fixedSubgroup θ)) := by
  rw [fixedSubgroup_inv_mul_mul_eq_map, ← CFSG.Quasithin.map_perfectCore]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

end Conj

section Aut

variable {K : Type} [Field K] [Finite K]

theorem statedClassicalModel_statedPlus_four {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4 2 f :=
  ⟨⟨Nat.prime_two, hf, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩

theorem odd_index_matrixProjectiveImage_plus_four {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    Odd (matrixProjectiveImage (coordinateQuadPlus 4 K)).index := by
  rw [← coordinate_plus_family_eq_matrixImage (statedClassicalModel_statedPlus_four hf hK) K hK
    (MulEquiv.refl _)]
  have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
      (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
    MulAction.index_stabilizer _ _
  rw [hst, ← Nat.card_coe_set_eq]
  rcases (CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy.plus_four_conjugacy
    (K := K)).2 with h | h <;> rw [h] <;> decide

theorem factorization_two_card_mulAut_coordinatePlus_four {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    (Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))).factorization 2 ≤
      f * (4 * (4 - 1)) + 1 + f.factorization 2 := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hmod := statedClassicalModel_statedPlus_four hf hK
  have hab :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_model_isometry_abelianization_order_bound
    _ .POmegaPlus (.inr (.inl rfl)) 4 2 f hmod K hK (CFSG.LieType.Universal.Spin.quadPlus 4 K)
    (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K) (MulEquiv.refl _)
  obtain ⟨h2, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.ordProj_two_card_outer_reindex_le
      Nat.prime_two hf hK (plusIndexEquiv 4) (CFSG.LieType.Universal.Spin.quadPlus 4 K) hab
      (Qc := coordinateQuadPlus 4 K) rfl
      (coordinate_model_intrinsic_plus hmod K hK (MulEquiv.refl _)).1
  have hout := h2 rfl
  rw [CFSG.LocalAnalysis.ComponentInitial.ordProj_two_eq_one_of_odd
    (odd_index_matrixProjectiveImage_plus_four hf hK), mul_one] at hout
  have := factorization_two_card_mulAut_le
    (conj_injective_coordinatePlus (K := K) (by norm_num : 3 ≤ 4)) hout
  rwa [card_coordinatePlus hf hK le_rfl, factorization_two_ordD hf (by norm_num)] at this

end Aut

section Bounds

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem omegaInvolutionBound_of_mem_image (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    (hI : OmegaLinearInvolutionTwoPart Q n f) {θ : MulAut (matrixProjectiveDerived Q)}
    (hα : θ ∈ matrixProjectiveImage Q) (hθθ : θ * θ = 1) (hθ1 : θ ≠ 1) :
    f * (n * (n - 1) + 4) ≤ 2 * (Nat.card (fixedSubgroup θ)).factorization 2 ∨
      ∃ g : ℕ, f = 2 * g ∧ (ordD n (2 ^ g) ∣ Nat.card (perfectCore (fixedSubgroup θ)) ∨
        ordTwistedD n (2 ^ g) ∣ Nat.card (perfectCore (fixedSubgroup θ))) := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hθ2 : orderOf θ = 2 := orderOf_eq_prime (by rw [sq]; exact hθθ) hθ1
  obtain ⟨S, hS, hSθ⟩ := CFSG.ComponentClassification.UnbalancedCatalog.exists_unit_rep hα
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
  · exact Or.inr (exists_dvd_card_perfectCore_fixedSubgroup_of_field hf hK hn hQ hT hE hα hθ2 hS
      hSθ hσ)

theorem omegaInvolutionBoundsDvd_coordinatePlus_four (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    OmegaInvolutionBoundsDvd (matrixProjectiveDerived (coordinateQuadPlus 4 K)) 4 f := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hreg := regular_coordinateQuadPlus 4 K (by norm_num)
  intro θ hθθ hθ1
  obtain ⟨β, hβ⟩ :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy.plus_four_conjugacy
      (K := K)).1 θ hθθ
  rw [coordinate_plus_family_eq_matrixImage (statedClassicalModel_statedPlus_four hf hK) K hK
    (MulEquiv.refl _)] at hβ
  have hθ'θ' : β⁻¹ * θ * β * (β⁻¹ * θ * β) = 1 := by
    calc β⁻¹ * θ * β * (β⁻¹ * θ * β) = β⁻¹ * (θ * θ) * β := by group
      _ = 1 := by rw [hθθ, mul_one, inv_mul_cancel]
  have hθ'1 : β⁻¹ * θ * β ≠ 1 := fun h => hθ1 (by
    calc θ = β * (β⁻¹ * θ * β) * β⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel])
  have key := omegaInvolutionBound_of_mem_image hf hK le_rfl hreg.1 hreg.2
    (commutator_coordinateQuadPlus 4 K (by norm_num))
    (omegaLinearInvolutionTwoPart_coordinatePlus_four hK) hβ hθ'θ' hθ'1
  rwa [card_fixedSubgroup_inv_mul_mul, card_perfectCore_fixedSubgroup_inv_mul_mul] at key

theorem swapPairExclusion_coordinatePlus_four (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
  swapPairExclusion_of_involutionBoundsDvd le_rfl hf
    (Or.inl (card_coordinatePlus (by omega) hK le_rfl))
    (factorization_two_card_mulAut_coordinatePlus_four (by omega) hK)
    (omegaInvolutionBoundsDvd_coordinatePlus_four (by omega) hK)

theorem omegaPlusLinearInvolutionInput_four : OmegaPlusLinearInvolutionInput 4 := by
  intro K F _ _ _ _ _ _ hFK s hss hdvd
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hF : Nat.card F = 2 ^ (2 * f) := by rw [hFK, hK, ← pow_mul, mul_comm]
  have := finite_mulAut_matrixProjectiveDerived (coordinateQuadPlus 4 K)
  have hAut := factorization_two_card_mulAut_coordinatePlus_four hf hK
  have h2A := factorization_two_two_mul_le
    (Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
  have hvf : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hle := factorization_two_le_of_dvd_ne_zero hdvd (mul_ne_zero two_ne_zero Nat.card_pos.ne')
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one, map_one, fixedSubgroup_one_eq_top, Subgroup.card_top,
      card_coordinatePlus (by omega) hF le_rfl, factorization_two_ordD (by omega) (by norm_num)]
      at hle
    omega
  · have h := omegaLinearInvolutionTwoPart_coordinatePlus_four hF s hss hs1
    omega

end Bounds

end CFSG.SeitzReduction.OmegaPilot
