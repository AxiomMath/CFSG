module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerAbs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
open scoped commutatorElement

universe u v

theorem commutator_eq_of_quasisimple_normal {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [IsMulCommutative (G ⧸ N)] (hN : CFSG.IsQuasisimple ↥N) : commutator G = N := by
  apply le_antisymm
  · rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' N) ⁅g₁, g₂⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (IsMulCommutative.is_comm.comm _ _)
  · have h1 : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.mp (by exact hN.1)
    rw [← h1, commutator_def]
    exact Subgroup.commutator_mono le_top le_top

theorem isQuasisimple_commutator_of_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : CFSG.IsQuasisimple ↥(commutator G')) : CFSG.IsQuasisimple ↥(commutator G) := by
  have hmap : (commutator G).map e.toMonoidHom = commutator G' := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ e.surjective]
    rw [commutator_def]
  have e1 : ↥(commutator G) ≃* ↥((commutator G).map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  have h' : CFSG.IsQuasisimple ↥((commutator G).map e.toMonoidHom) := by
    rw [hmap]; exact h
  exact isQuasisimple_of_equiv e1.symm h'

section Branches

variable {K : Type u} [Field K] [Finite K] {V : Type v}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem isQuasisimple_commutator_nonsquare [Nontrivial V] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (T : Module.End K V) (d : K) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (hadj : ∀ x y, Q.polarBilin (T x) y = -Q.polarBilin x (T y))
    (hdim : 6 ≤ Module.finrank K V) :
    CFSG.IsQuasisimple ↥(commutator ↥(orthogonalOperatorCentralizer Q T)) := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  let := scalarAlgebra_finite_type T d hns hsquare
  let := evaluationModule_finite T
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  let h := actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj
  have hsig : (conjugation T d hns hsquare).toRingEquiv ^ 2 = 1 := by
    apply RingEquiv.ext
    intro z
    change conjugation T d hns hsquare (conjugation T d hns hsquare z) = z
    exact conjugation_involutive T d hns hsquare z
  have hne : (conjugation T d hns hsquare).toRingEquiv ≠ 1 := by
    intro heq
    apply conjugation_ne_one T d hns hsquare h2
    apply AlgEquiv.ext
    intro z
    exact congrArg (fun s : scalarAlgebra T ≃+* scalarAlgebra T => s z) heq
  have hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield (scalarAlgebra T)
      (conjugation T d hns hsquare).toRingEquiv) ≠ 2 := by
    rw [CatalogueBOrthogonalLinearFixed.scalarFixedField_card T d hns hsquare h2]
    intro heq
    have hh := hodd
    rw [heq] at hh
    norm_num at hh
  have hfr : Module.finrank K V = 2 * Module.finrank (scalarAlgebra T) V :=
    evaluationModule_finrank T d hns hsquare
  have hn3 : 3 ≤ Module.finrank (scalarAlgebra T) V := by omega
  have hSU := CatalogueBUnitaryIsometry.isometry_all_dimensions_nonsmall h
    (actualNegativeHermitian_isSymm Q T d hd hns hsquare hadj)
    (actualNegativeHermitian_nondegenerate Q T d hd hns hsquare hadj hQ)
    hsig hne (by omega) hq2 (by omega) (by simp only [ne_eq, Prod.mk.injEq]; omega)
  have hcomm : commutator ↥(CatalogueBUnitaryIsometry.isometryGroup h) =
      CatalogueBUnitaryIsometry.specialIsometry h :=
    commutator_eq_of_quasisimple_normal _ hSU.1
  exact isQuasisimple_commutator_of_equiv
    (actualNegativeCentralizerEquiv Q T d hd hns hsquare hadj h2) (by rw [hcomm]; exact hSU.1)

theorem isQuasisimple_commutator_split (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ b : K) (hd : d ≠ 0) (hb : b ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hnegative : μ / d = -1) (hdim : 6 ≤ Module.finrank K V) :
    CFSG.IsQuasisimple ↥(commutator ↥(orthogonalOperatorCentralizer Q A.toLinearMap)) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hgeom := negative_square_kernel_geometry Q hQ A d μ b hd hb h2 hsquare hroot hsim hnegative
  have hfr : Module.finrank K (positiveSquareKernel A b) = Module.finrank K V / 2 :=
    hgeom.2.2.2.2.1
  set n := Module.finrank K (positiveSquareKernel A b) with hn
  have hn3 : 3 ≤ n := by omega
  have hq : CFSG.IsQuasisimple (CatalogueBGeneralLinear.specialLinearRange n K) :=
    CatalogueBGeneralLinear.specialLinearRange_quasisimple n K (by omega) (Or.inl (by omega))
      (Or.inl (by omega))
  have := CatalogueBGeneralLinear.specialLinearRangeNormal n K
  have := CatalogueBGeneralLinear.determinantQuotient_commutative n K
  have hcomm := commutator_eq_of_quasisimple_normal
    (CatalogueBGeneralLinear.specialLinearRange n K) hq
  have e₁ := negativeSquareKernelCentralizerEquiv Q hQ A d μ b hd hb h2 hsquare hroot hsim
    hnegative
  let bas := Module.finBasis K (positiveSquareKernel A b)
  have e₂ : (positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b) ≃*
      Matrix.GeneralLinearGroup (Fin n) K :=
    CatalogueBAlternatingIsometry.basisMatrixEquiv bas
  exact isQuasisimple_commutator_of_equiv (e₁.trans e₂) (by rw [hcomm]; exact hq)

theorem isQuasisimple_commutator_cplx (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hA2 : ∀ x, A (A x) = -x) (hdim : 6 ≤ Module.finrank K V) :
    CFSG.IsQuasisimple ↥(commutator ↥(orthogonalOperatorCentralizer Q A.toLinearMap)) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hsq : ∀ x : V, A (A x) = ((-1 : K)) • x := fun x => by rw [hA2, neg_one_smul]
  have hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (1 : K) * Q.polarBilin x y := fun x y => by
    rw [one_mul]
    exact CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hAO x y
  have hd : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  by_cases hs : IsSquare (-1 : K)
  · obtain ⟨b, hb⟩ := hs
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb
    exact isQuasisimple_commutator_split hodd Q hQ A (-1) 1 b hd hb0 hsq (by rw [hb]; ring) hsim
      (by simp) hdim
  · have hT : A.toLinearMap ^ 2 = algebraMap K (Module.End K V) (-1) := by
      ext x
      change A (A x) = (-1 : K) • x
      exact hsq x
    have hadj : ∀ x y, Q.polarBilin (A.toLinearMap x) y = -Q.polarBilin x (A.toLinearMap y) :=
      negative_square_adjoint Q A (-1) 1 hd hsq hsim (by simp)
    exact isQuasisimple_commutator_nonsquare hodd Q hQ A.toLinearMap (-1) hd hs hT hadj hdim

end Branches

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
