module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic
import CFSG.Quasithin.Background.P3OrthoOm4

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (commSpace omegaGroup mem_omegaGroup omegaGroup_le
  relIndex_omegaGroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus coordinatePlusIsometry)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit (specialImage tau)

section SplitFour

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

theorem omegaGroup_le_orthDerived_of_splitFour (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 4) (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0)
    (hq : 4 ≤ Nat.card K) : omegaGroup R hR ≤ orthDerived R := by
  classical
  have hq2 : Nat.card K ≠ 2 := by omega
  have hq3 : Nat.card K ≠ 3 := by omega
  obtain ⟨-, -, -, hcov4, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
      R hR (Or.inr (Or.inr ⟨hdim, hS⟩))
  obtain ⟨-, e, -, -, hcomm, -⟩ := hcov4 hdim hS hq2 hq3
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hJ : commutator (TauCeti.QuadraticMap.orthogonalGroup R) =
      (specialImage K).map e.symm.toMonoidHom := by
    rw [hcomm, ← Subgroup.map_sup, CFSG.LocalAnalysis.ComponentInitial.determinantFactors_sup]
  have hder : (commutator (TauCeti.QuadraticMap.orthogonalGroup R)).map
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype = orthDerived R := by
    rw [Subgroup.map_subtype_commutator]
  have hmemJ : ∀ g : TauCeti.QuadraticMap.orthogonalGroup R, e g ∈ specialImage K →
      (g : W ≃ₗ[K] W) ∈ orthDerived R := by
    intro g hg
    rw [← hder]
    refine ⟨g, ?_, rfl⟩
    rw [hJ]
    exact ⟨e g, hg, by simp⟩
  have hNΩ : orthDerived R ≤ omegaGroup R hR :=
    CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR
  set τ' : TauCeti.QuadraticMap.orthogonalGroup R := e.symm tau with hτ'
  have hτ : ∀ g : TauCeti.QuadraticMap.orthogonalGroup R, e g ∉ specialImage K →
      (g : W ≃ₗ[K] W) * (τ' : W ≃ₗ[K] W) ∈ orthDerived R := by
    intro g hg
    have h := (CFSG.Quasithin.G11.P3Ortho.Om4.mem_specialImage_or_mul_tau (e g)).resolve_left hg
    have he : e (g * τ') = e g * tau := by
      rw [map_mul, hτ', MulEquiv.apply_symm_apply]
    have := hmemJ (g * τ') (by rw [he]; exact h)
    simpa using this
  have hτΩ : (τ' : W ≃ₗ[K] W) ∉ omegaGroup R hR := by
    intro hτΩ
    have hle : TauCeti.QuadraticMap.orthogonalGroup R ≤ omegaGroup R hR := by
      intro g hg
      by_cases hJg : e ⟨g, hg⟩ ∈ specialImage K
      · exact hNΩ (hmemJ ⟨g, hg⟩ hJg)
      · have h1 := hNΩ (hτ ⟨g, hg⟩ hJg)
        have h2 : g = (g * (τ' : W ≃ₗ[K] W)) * (τ' : W ≃ₗ[K] W)⁻¹ := by group
        rw [h2]
        exact mul_mem h1 (inv_mem hτΩ)
    have h1 := relIndex_omegaGroup R hR
    rw [Subgroup.relIndex_eq_one.mpr hle] at h1
    omega
  intro g hg
  have hgO := omegaGroup_le R hR hg
  by_contra hgD
  have hJg : e ⟨g, hgO⟩ ∉ specialImage K := fun h => hgD (hmemJ _ h)
  apply hτΩ
  have h1 := hNΩ (hτ ⟨g, hgO⟩ hJg)
  have h2 : (τ' : W ≃ₗ[K] W) = g⁻¹ * (g * (τ' : W ≃ₗ[K] W)) := by group
  rw [h2]
  exact mul_mem (inv_mem hg) h1

omit [CharP K 2] in
theorem commutator_orthDerived_of_splitFour (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 4) (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0)
    (hq : 4 ≤ Nat.card K) : ⁅orthDerived R, orthDerived R⁆ = orthDerived R := by
  obtain ⟨-, hgen, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
      R hR (Or.inr (Or.inr ⟨hdim, hS⟩))
  have hsmall : ¬ ((finrank K W = 3 ∧ Nat.card K = 3) ∨
      ((finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) ∧
        (Nat.card K = 2 ∨ Nat.card K = 3))) := by
    rintro (⟨h3, -⟩ | ⟨-, h23⟩)
    · omega
    · omega
  obtain ⟨hP, -⟩ := hgen hsmall
  have hder : (commutator (TauCeti.QuadraticMap.orthogonalGroup R)).map
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype = orthDerived R := by
    rw [Subgroup.map_subtype_commutator]
  have e₁ : commutator (TauCeti.QuadraticMap.orthogonalGroup R) ≃* orthDerived R :=
    ((commutator (TauCeti.QuadraticMap.orthogonalGroup R)).equivMapOfInjective
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype_injective).trans
      (MulEquiv.subgroupCongr hder)
  have hP' : Group.IsPerfect (orthDerived R) :=
    Group.IsPerfect.ofSurjective (f := e₁.toMonoidHom) e₁.surjective
  exact Subgroup.isPerfect_iff.1 hP'

end SplitFour

section StabTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem splitFour_plusPerp_three (j' : Fin 3) :
    (polarBilin ((coordinateQuadPlus 3 K).comp
      (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))).subtype)).Nondegenerate ∧
    finrank K (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))) = 4 ∧
    ∃ S : Submodule K (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))),
      finrank K S = 2 ∧ ∀ x ∈ S, (coordinateQuadPlus 3 K).comp
        (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))).subtype x = 0 := by
  have e : (CFSG.LieType.Universal.Spin.quadPlus (3 - 1) K).IsometryEquiv
      ((coordinateQuadPlus 3 K).comp
        (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))).subtype) :=
    (coordinatePlusIsometry (3 - 1) K).trans (plusPerpIsometry (K := K) (by norm_num) j').symm
  let f : (Fin (3 - 1) → K) →ₗ[K] (Fin (3 - 1) ⊕ Fin (3 - 1) → K) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := fun x y => by ext (i | i) <;> simp
      map_smul' := fun c x => by ext (i | i) <;> simp }
  have hf : Function.Injective f := fun x y h => funext fun i => by
    have := congrFun h (.inl i)
    simpa [f] using this
  have hT : finrank K (LinearMap.range f) = 2 := by
    rw [LinearMap.finrank_range_of_inj hf, Module.finrank_fin_fun]
  have hT0 : ∀ v ∈ LinearMap.range f, CFSG.LieType.Universal.Spin.quadPlus (3 - 1) K v = 0 := by
    rintro _ ⟨x, rfl⟩
    rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
    simp [f]
  refine ⟨CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.polar_nondegenerate_isometry
    e (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (3 - 1) K), ?_,
    (LinearMap.range f).map e.toLinearMap, ?_,
    CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.submodule_singular_isometry e _
      hT0⟩
  · rw [← e.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
    simp
  · rw [CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.submodule_finrank_isometry,
      hT]

theorem commutator_stabTwoBar_four (hq : 4 ≤ Nat.card K) {i j : Fin 4} (hij : i ≠ j) :
    ⁅stabTwoBar K i j, stabTwoBar K i j⁆ = stabTwoBar K i j := by
  obtain ⟨j', hj'⟩ := exists_avoid_eq (M := 4 - 1) (by omega : 4 - 1 + 1 = 4) hij.symm
  obtain ⟨hR, hdim, hS⟩ := splitFour_plusPerp_three (K := K) j'
  have hΩ := omegaGroup_le_orthDerived_of_splitFour hR hdim hS hq
  have φ := (stabTwoBarEquiv (K := K) (n := 4) (by omega) hj').trans
    ((isHypCoord_coordinateQuadPlus (K := K) (n := 4 - 1) j').stabDerivedEquivOfLe
      (regular_coordinateQuadPlus (4 - 1) K (by omega)).1 hR hΩ)
  have hP : Group.IsPerfect (orthDerived ((coordinateQuadPlus 3 K).comp
      (perpSub K (plusIndexEquiv 3 (.inl j')) (plusIndexEquiv 3 (.inr j'))).subtype)) :=
    Subgroup.isPerfect_iff.2 (commutator_orthDerived_of_splitFour hR hdim hS hq)
  exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom)
    φ.symm.surjective)

end StabTwo

end CFSG.SeitzReduction.OmegaPilot
