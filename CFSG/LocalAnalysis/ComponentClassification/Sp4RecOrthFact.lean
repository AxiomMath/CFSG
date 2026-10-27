module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthWitness
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthFour
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLowDimensionFrontiers
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGL

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_plane_reflection (hodd : Odd (Nat.card K)) {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate) (hW : 3 ≤ finrank K W) :
    ∃ t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      t * t = 1 ∧ ∃ v₁ v₂ : W, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ t v₁ = -v₁ ∧ t v₂ = v₂ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have hsymm : LinearMap.BilinForm.IsSymm Q.polarBilin :=
    ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  obtain ⟨hval, hbas⟩ :=
    LocalAnalysis.ComponentInitial.finite_odd_symmetric_equal_value_orthogonal_basis
      hodd rfl (by omega : 2 ≤ finrank K W) hQ hsymm
  obtain ⟨m0, hm0⟩ := hval 2 h2
  obtain ⟨e, heo, -, hea, -⟩ := hbas 2 m0 h2 hm0
  set i₀ : Fin (finrank K W) := ⟨0, by omega⟩
  set i₁ : Fin (finrank K W) := ⟨1, by omega⟩
  set i₂ : Fin (finrank K W) := ⟨2, by omega⟩
  have hQe : ∀ i : Fin (finrank K W), (i : ℕ) < finrank K W - 1 → Q (e i) = 1 := by
    intro i hi
    have h := hea i hi
    change polar Q (e i) (e i) = 2 at h
    rw [OddClassSelector.polar_self_eq] at h
    exact mul_left_cancel₀ h2 (h.trans (mul_one 2).symm)
  have hQ₀ : Q (e i₀) = 1 := hQe i₀ (by simp [i₀]; omega)
  have hQ₁ : Q (e i₁) = 1 := hQe i₁ (by simp [i₁]; omega)
  have horth : ∀ i j : Fin (finrank K W), i ≠ j → polar Q (e i) (e j) = 0 := fun i j hij =>
    heo hij
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  refine ⟨reflect Q (e i₀) * reflect Q (e i₁), OddClassSelector.reflect_mul_reflect_mem h2
    (by rw [hQ₀]; exact one_ne_zero) (by rw [hQ₁]; exact one_ne_zero) ⟨1, by rw [hQ₀, hQ₁]⟩,
    ?_, e i₀, e i₂, e.ne_zero _, e.ne_zero _, ?_, ?_⟩
  · rw [show reflect Q (e i₀) * reflect Q (e i₁) * (reflect Q (e i₀) * reflect Q (e i₁)) =
      reflect Q (e i₀) * (reflect Q (e i₁) * reflect Q (e i₀)) * reflect Q (e i₁) by group,
      ← OddClassSelector.reflect_comm_of_polar_eq_zero (horth i₀ i₁ h01)]
    rw [show reflect Q (e i₀) * (reflect Q (e i₀) * reflect Q (e i₁)) * reflect Q (e i₁) =
      (reflect Q (e i₀) * reflect Q (e i₀)) * (reflect Q (e i₁) * reflect Q (e i₁)) by group,
      reflect_mul_self, reflect_mul_self, one_mul]
  · rw [LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero (horth i₁ i₀ h01.symm),
      reflect_apply (by rw [hQ₀]; exact one_ne_zero), OddClassSelector.polar_self_eq, hQ₀]
    rw [mul_one, div_one, two_smul]
    abel
  · rw [LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero (horth i₁ i₂ h12),
      reflect_apply_of_polar_eq_zero (horth i₀ i₂ h02)]

section Det

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplitComponents
open CFSG.LocalAnalysis.ComponentInitial (determinantLeftFactor determinantRightFactor)

theorem det_pComponent_eq_factor (hq2 : Nat.card K ≠ 2) (hq3 : Nat.card K ≠ 3)
    {L : Subgroup (DeterminantIsometries K)} (hL : IsPComponent 2 L) :
    L = determinantLeftFactor K ∨ L = determinantRightFactor K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hr⟩ := CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient 2
    (specialImage K) L hL
  obtain ⟨J, hJ, hJmap, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2
    specialLinearCover specialLinearCover_surjective specialLinearCover_kernel_central _ hr
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hq2)
    (Or.inr hq3)
  have htop : ∀ U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K), IsPComponent 2 U → U = ⊤ :=
    fun U hU => CatalogueBAlternatingIsometry.pComponent_eq_top_of_quasisimple hSL 2 U hU
  have hL' : L = J.map ((specialImage K).subtype.comp specialLinearCover) := by
    rw [← map_map, hJmap, map_subgroupOf_eq_of_le hle]
  rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2 J hJ with
    hl | hr'
  · left
    rw [hL', hl, htop _ (isPComponent_fst hJ hl)]
    ext z
    constructor
    · rintro ⟨⟨a, b⟩, ⟨-, hb⟩, rfl⟩
      have hb' : b = 1 := hb
      subst hb'
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a, 1), ⟨mem_top a, one_mem _⟩, rfl⟩
  · right
    rw [hL', hr', htop _ (isPComponent_snd hJ hr')]
    ext z
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, -⟩, rfl⟩
      have ha' : a = 1 := ha
      subst ha'
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(1, b), ⟨one_mem _, mem_top b⟩, rfl⟩

theorem orth_pComponent_cases (hodd : Odd (Nat.card K)) {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate) {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
    (hM : IsPComponent 2 M) :
    M = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ∨
      (finrank K W = 4 ∧ ∃ j ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q),
        (∀ v, (j : W ≃ₗ[K] W) ((j : W ≃ₗ[K] W) v) = -v) ∧ ∀ u ∈ M, u * j = j * u) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have hq2 : Nat.card K ≠ 2 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
  have hleft : IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) →
      M = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := fun hq =>
    (CatalogueBOrthogonal.pComponent_eq_derived_of_quasisimple hq 2 Nat.prime_two M hM).1
  by_cases h5 : 5 ≤ finrank K W
  · exact Or.inl (hleft (OddSelector.commutator_orthogonalGroup_quasisimple hodd Q hQ h5))
  by_cases hle2 : finrank K W ≤ 2
  · exact (CatalogueBOrthogonal.orthogonal_small_no_pComponent Q h2 hQ hle2 2 M hM).elim
  rcases (by omega : finrank K W = 3 ∨ finrank K W = 4) with h3 | h4
  · have hcov :=
      LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
        Q hQ (Or.inl ⟨hodd, Or.inl h3⟩)
    by_cases hq3 : Nat.card K = 3
    · exact (((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_three_p_components_frontier
        hodd Q hQ h3).2 hq3).2 2 Nat.prime_two M hM).elim
    · obtain ⟨-, -, -, -, -, -, hq⟩ := hcov.2.2.1 hodd h3 hq3
      exact Or.inl (hleft hq)
  · have hcov :=
      LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
        Q hQ (Or.inl ⟨hodd, Or.inr (Or.inl h4)⟩)
    by_cases hsp : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    · by_cases hq3 : Nat.card K = 3
      · obtain ⟨S, hS2, hSQ⟩ := hsp
        exact (CatalogueBOrthogonalFourSplitComponents.orthogonal_four_split_three_no_pComponent
          hq3 Q hQ h4 S hS2 hSQ 2 M hM).elim
      right
      refine ⟨h4, ?_⟩
      obtain ⟨ψ, e, -, he, hsup, -⟩ := hcov.2.2.2.1 h4 hsp hq2 hq3
      have hval : ∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (v : W),
          (g : W ≃ₗ[K] W) v = ψ.symm ((e g).val (ψ v)) := by
        intro g v
        rw [he, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      obtain ⟨J₀, hJ₀, -⟩ := OddClassSelector.exists_rotation K
      rcases det_pComponent_eq_factor hq2 hq3
          (CatalogueBAlternating.pComponent_map_equiv 2 e _ hM) with hl | hr
      · refine ⟨e.symm (CatalogueBOrthogonalFourSplit.specialRho (1, J₀⁻¹)), ?_, ?_, ?_⟩
        · rw [hsup]
          exact mem_sup_right ⟨_, ⟨J₀⁻¹, rfl⟩, rfl⟩
        · intro v
          rw [hval, hval, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
            CatalogueBOrthogonalFourSplit.specialRho_apply,
            CatalogueBOrthogonalFourSplit.specialRho_apply]
          simp only [inv_inv, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_assoc]
          rw [hJ₀, Matrix.mul_neg, Matrix.mul_one, map_neg, LinearEquiv.symm_apply_apply]
        · intro u hu
          apply e.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
          have hu' : e u ∈ LocalAnalysis.ComponentInitial.determinantLeftFactor K := by
            rw [← hl]
            exact ⟨u, hu, rfl⟩
          exact LocalAnalysis.ComponentInitial.determinantFactors_commute hu' ⟨J₀⁻¹, rfl⟩
      · refine ⟨e.symm (CatalogueBOrthogonalFourSplit.specialRho (J₀, 1)), ?_, ?_, ?_⟩
        · rw [hsup]
          exact mem_sup_left ⟨_, ⟨J₀, rfl⟩, rfl⟩
        · intro v
          rw [hval, hval, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
            CatalogueBOrthogonalFourSplit.specialRho_apply,
            CatalogueBOrthogonalFourSplit.specialRho_apply]
          simp only [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, ← Matrix.mul_assoc]
          rw [hJ₀, Matrix.neg_mul, Matrix.one_mul, map_neg, LinearEquiv.symm_apply_apply]
        · intro u hu
          apply e.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
          have hu' : e u ∈ LocalAnalysis.ComponentInitial.determinantRightFactor K := by
            rw [← hr]
            exact ⟨u, hu, rfl⟩
          exact (LocalAnalysis.ComponentInitial.determinantFactors_commute ⟨J₀, rfl⟩ hu').symm
    · obtain ⟨-, -, -, -, -, -, -, -, hq⟩ := hcov.2.2.2.2.1 hodd h4 hsp
      exact Or.inl (hleft hq)

end Det

end CFSG.ComponentClassification.Sp4Rec
