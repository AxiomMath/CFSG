module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataGeometry

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointKernel
  (similarityPointAction_kernel_actions)

theorem eq_of_orderOf_eq_two_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  have := Fintype.ofFinite G
  have hd : 2 ∣ Fintype.card G := hx ▸ orderOf_dvd_card
  have h := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : x ∈ ({a} : Finset G) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hya : y ∈ ({a} : Finset G) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [Finset.mem_singleton] at hxa hya
  rw [hxa, hya]

variable {K : Type} [Field K] {d : ℕ}

theorem eq_one_of_mul_self_eq_one_of_charTwo [CharP K 2] {c : K} (hc : c * c = 1) : c = 1 := by
  rcases mul_self_eq_one_iff.mp hc with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

theorem scalar_mulVec_eq_smul (b : K) (v : Fin d → K) : Matrix.scalar (Fin d) b *ᵥ v = b • v := by
  funext i
  simp [Matrix.scalar_apply]

theorem exists_ne_zero_of_polar_nondegenerate (hd : 1 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) : ∃ v, Q v ≠ 0 := by
  by_contra h
  push Not at h
  have hv : (Pi.single ⟨0, hd⟩ 1 : Fin d → K) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 ⟨0, hd⟩
    simp at h1
  refine hv (hQ.1 _ fun w => ?_)
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h, h, h, sub_zero, sub_zero]

theorem matrixDerivedScalars_eq_bot_of_charTwo [CharP K 2] (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) : matrixDerivedScalars Q = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q A).mp hA
  have hiso := (mem_matrixIsometries_iff Q A.val).mp (matrixDerived_le_isometries Q A.2)
  obtain ⟨v, hv⟩ := hQ
  have h1 := hiso v
  rw [← hc, matrixLinearEquiv_apply, GeneralLinearGroup.coe_scalar, scalar_mulVec_eq_smul,
    QuadraticMap.map_smul, smul_eq_mul] at h1
  have hc1 : c = 1 := Units.ext (eq_one_of_mul_self_eq_one_of_charTwo
    (mul_right_cancel₀ hv (h1.trans (one_mul _).symm)))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

@[expose] def unitMultiplierPairs (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (similarityPairs Q) where
  carrier := {g | ∀ v, Q (coordinateSemilinearMap g.val v) = g.val.right (Q v)}
  one_mem' := fun v => by
    change Q (coordinateSemilinearMap 1 v) = Q v
    rw [coordinateSemilinearMap_one]
  mul_mem' := by
    intro g h hg hh v
    change Q (coordinateSemilinearMap (g.val * h.val) v) = g.val.right (h.val.right (Q v))
    rw [coordinateSemilinearMap_mul, hg, hh]
  inv_mem' := by
    intro g hg v
    change Q (coordinateSemilinearMap g.val⁻¹ v) = g.val.right.symm (Q v)
    rw [coordinateSemilinearMap_inv]
    apply g.val.right.injective
    rw [← hg, AddEquiv.apply_symm_apply]
    exact (g.val.right.apply_symm_apply (Q v)).symm

theorem mem_unitMultiplierPairs_iff (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q) :
    g ∈ unitMultiplierPairs Q ↔
      ∀ v, Q (coordinateSemilinearMap g.val v) = g.val.right (Q v) :=
  Iff.rfl

theorem mem_unitMultiplierPairs_iff_multiplier (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q) :
    g ∈ unitMultiplierPairs Q ↔ multiplier Q g = 1 := by
  constructor
  · intro hg
    refine multiplier_unique Q hQ g.val _ 1 (multiplier_spec Q g) fun v => ?_
    rw [Units.val_one, one_mul]
    exact hg v
  · intro hg v
    rw [multiplier_spec, hg, Units.val_one, one_mul]

theorem scalarPair_mem (Q : QuadraticForm K (Fin d → K)) (b : Kˣ) :
    SemidirectProduct.inl (GeneralLinearGroup.scalar (Fin d) b) ∈ similarityPairs Q := by
  refine ⟨b * b, fun v => ?_⟩
  rw [coordinateSemilinearMap_inl, matrixLinearEquiv_apply, GeneralLinearGroup.coe_scalar,
    scalar_mulVec_eq_smul, QuadraticMap.map_smul, smul_eq_mul, Units.val_mul]
  rfl

theorem kappa_scalarPair (Q : QuadraticForm K (Fin d → K)) (b : Kˣ) :
    matrixProjectiveConjugationHom Q ⟨_, scalarPair_mem Q b⟩ = 1 := by
  have hz : GeneralLinearGroup.scalar (Fin d) b ∈ Subgroup.center (GL (Fin d) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨b, rfl⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixProjectiveConjugation Q _ (matrixProjectiveProjection Q A) =
    matrixProjectiveProjection Q A
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_val]
  change GeneralLinearGroup.scalar (Fin d) b *
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K 1 A.val *
        (GeneralLinearGroup.scalar (Fin d) b)⁻¹ = A.val
  rw [map_one, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hz A.val, mul_inv_cancel_right]

theorem exists_scalarPair_mul_mem [Finite K] [CharP K 2] (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    ∃ b : Kˣ, (⟨_, scalarPair_mem Q b⟩ * g : similarityPairs Q) ∈ unitMultiplierPairs Q := by
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
    (((multiplier Q g)⁻¹ : Kˣ) : K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact Units.ne_zero _ hc
  refine ⟨Units.mk0 c hc0, fun v => ?_⟩
  change Q (coordinateSemilinearMap (SemidirectProduct.inl (GeneralLinearGroup.scalar (Fin d)
    (Units.mk0 c hc0)) * g.val) v) = g.val.right (Q v)
  rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_inl, matrixLinearEquiv_apply,
    GeneralLinearGroup.coe_scalar, scalar_mulVec_eq_smul, QuadraticMap.map_smul, smul_eq_mul,
    multiplier_spec, Units.val_mk0, ← mul_assoc, ← hc, Units.inv_mul, one_mul]

section Kernel

variable (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)

include hQ hT hE in
theorem eq_one_of_kappa_eq_one [CharP K 2] (hd : 1 ≤ d) {g : similarityPairs Q}
    (hg : g ∈ unitMultiplierPairs Q) (hκ : matrixProjectiveConjugationHom Q g = 1) : g = 1 := by
  have hrho :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointKernel.projectivePointAction_injective
      Q hQ hT
  have hs := projectivePointStabilizer_injective_native Q hE hQ hT
  have h1 := pointFamilyNormalizerEquiv_similarity Q hrho hs g
  have h2 : (⟨matrixProjectiveConjugationHom Q g, projective_image_le_pointFamilyAut Q ⟨g, rfl⟩⟩ :
      projectivePointFamilyAut Q) = 1 := Subtype.ext hκ
  rw [h2, map_one] at h1
  obtain ⟨hσ, a, ha, -, -, -, hμ⟩ := similarityPointAction_kernel_actions Q hQ hT g h1.symm
  rw [(mem_unitMultiplierPairs_iff_multiplier Q (exists_ne_zero_of_polar_nondegenerate hd hQ)
    g).mp hg, Units.val_one, sq] at hμ
  have ha1 : a = 1 := Units.ext (eq_one_of_mul_self_eq_one_of_charTwo hμ.symm)
  apply Subtype.ext
  apply SemidirectProduct.ext
  · rw [← ha, ha1, map_one]
    rfl
  · exact hσ

@[expose] noncomputable def unitKappa :
    unitMultiplierPairs Q →* MulAut (matrixProjectiveDerived Q) :=
  (matrixProjectiveConjugationHom Q).comp (unitMultiplierPairs Q).subtype

include hQ hT hE in
theorem unitKappa_injective [CharP K 2] (hd : 1 ≤ d) : Function.Injective (unitKappa Q) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact Subtype.ext (eq_one_of_kappa_eq_one Q hQ hT hE hd g.2 hg)

theorem range_unitKappa [Finite K] [CharP K 2] :
    (unitKappa Q).range = matrixProjectiveImage Q := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact ⟨g.1, rfl⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨b, hb⟩ := exists_scalarPair_mul_mem Q g
    refine ⟨⟨_, hb⟩, ?_⟩
    change matrixProjectiveConjugationHom Q (⟨_, scalarPair_mem Q b⟩ * g) = _
    rw [map_mul, kappa_scalarPair, one_mul]

end Kernel

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
