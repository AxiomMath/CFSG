module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherOuterNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPairOrbits
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPointSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem unitary_point_normal_generation (h : UnitaryFieldData p f K) (hn : 3 ≤ n)
    (hnq : (n, p ^ f) ≠ (3, 2)) {L : Submodule K (Fin n → K)} (hL : L ∈ isotropicLines h n) :
    Subgroup.closure (⋃ g : unitarySU p f K n,
      ((isotropicTransvectionGroup h n L).map (MulAut.conj g).toMonoidHom :
        Set (unitarySU p f K n))) = ⊤ := by
  set H := Subgroup.closure (⋃ g : unitarySU p f K n,
    ((isotropicTransvectionGroup h n L).map (MulAut.conj g).toMonoidHom :
      Set (unitarySU p f K n))) with hH
  obtain ⟨-, htrans, -⟩ := unitary_isotropic_pair_orbits h hn
  have hUM : ∀ M : Submodule K (Fin n → K), M ∈ isotropicLines h n →
      isotropicTransvectionGroup h n M ≤ H := by
    intro M hM
    obtain ⟨g, hg⟩ := htrans ⟨L, hL⟩ ⟨M, hM⟩
    have hgL : g • L = M := congrArg Subtype.val hg
    rw [← hgL, ← (unitary_point_conjugation h g hL).2.1]
    intro x hx
    exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨g, hx⟩)
  let φ : unitarySU p f K n →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* _).toMonoidHom.comp
      (unitarySU p f K n).subtype
  have hφ : ∀ g : unitarySU p f K n, ((φ g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      (Fin n → K) →ₗ[K] Fin n → K) =
        mulVecLin ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := fun g =>
    Matrix.GeneralLinearGroup.coe_toLin _
  have hφinj : Function.Injective φ := fun g g' hgg' =>
    Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective hgg')
  have hT : Subgroup.closure (unitaryTransvections h (stdHermForm h n)) ≤ H.map φ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, ha, c, hc, rfl⟩
    by_cases ha0 : a = 0
    · subst ha0
      refine ⟨1, H.one_mem, Units.ext ?_⟩
      rw [map_one, coe_hermTransvectionGL]
      refine LinearMap.ext fun x => ?_
      rw [hermTransvection_apply, smul_zero, add_zero]
      rfl
    have hM := span_mem_isotropicLines ha0 ha
    obtain ⟨u, hu, hua⟩ := exists_mem_isotropicTransvectionGroup h hM
      (Submodule.mem_span_singleton_self a) hc
    refine ⟨u, hUM _ hM hu, Units.ext ?_⟩
    change ((φ u : LinearMap.GeneralLinearGroup K (Fin n → K)) : (Fin n → K) →ₗ[K] Fin n → K) = _
    rw [hφ, hua, coe_hermTransvectionGL]
  have hgen := unitary_transvection_generation h (stdHermForm_isSymm h n)
    (stdHermForm_separatingLeft h n) (by rw [Module.finrank_fin_fun]; omega)
    (by rw [Module.finrank_fin_fun]; exact hnq)
  refine eq_top_iff.mpr fun g _ => ?_
  have hg : φ g ∈ sesqSpecialUnitaryGroup (stdHermForm h n) := by
    rw [stdHermForm_eq_gramForm]
    change Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) ∈ _
    rw [toLin_mem_sesqSpecialUnitaryGroup_iff, ← unitarySU_eq_gramSU]
    exact g.2
  rw [← hgen] at hg
  obtain ⟨u, hu, hug⟩ := hT hg
  rwa [← hφinj hug]

variable (h : UnitaryFieldData p f K) (n) in
@[expose, instance_reducible] noncomputable def unitaryProjMulAction :
    MulAction (unitaryPSU h n) (isotropicLines h n) :=
  MulAction.compHom _ (unitaryProjLineAction h n)

attribute [local instance] unitaryProjMulAction

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
