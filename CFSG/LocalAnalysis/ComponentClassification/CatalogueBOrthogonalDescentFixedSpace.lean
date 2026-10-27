module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalDescent

open CatalogueBLinearTwoDescent
open scoped TensorProduct

universe u v w

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

variable (sigma : K ≃+* K)

@[expose] def fixedSubspace (T : V ≃+ V)
    (hsemi : ∀ a x, T (a • x) = sigma a • T x) : Submodule (fixedSubfield K sigma) V where
  carrier := {x | T x = x}
  zero_mem' := T.map_zero
  add_mem' := by
    intro x y hx hy
    change T (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro a x hx
    change T ((a : K) • x) = (a : K) • x
    rw [hsemi, (mem_fixedSubfield K sigma a).mp a.property, hx]

theorem mem_fixedSubspace (T : V ≃+ V)
    (hsemi : ∀ a x, T (a • x) = sigma a • T x) (x : V) :
    x ∈ fixedSubspace sigma T hsemi ↔ T x = x := Iff.rfl

theorem fixedSubspace_scalar_apply (T : V ≃+ V)
    (hsemi : ∀ a x, T (a • x) = sigma a • T x)
    (a : fixedSubfield K sigma) (x : fixedSubspace sigma T hsemi) :
    ((a • x : fixedSubspace sigma T hsemi) : V) = (a : K) • (x : V) := rfl

theorem fixed_basis_repr_fixed {ι : Type w} [Fintype ι] (sigma : K ≃+* K)
    (T : V ≃+ V) (hsemi : ∀ a x, T (a • x) = sigma a • T x)
    (e : Module.Basis ι K V) (he : ∀ i, T (e i) = e i) (x : V) (hx : T x = x) (i : ι) :
    sigma (e.repr x i) = e.repr x i := by
  classical
  have hsum : (∑ j, sigma (e.repr x j) • e j) = x := by
    calc
      (∑ j, sigma (e.repr x j) • e j) = T (∑ j, e.repr x j • e j) := by
        rw [map_sum]
        simp only [hsemi, he]
      _ = T x := congrArg T (e.sum_repr x)
      _ = x := hx
  have h := congrArg (fun y => e.repr y i) hsum
  rw [congrFun (e.repr_sum_self _) i] at h
  exact h

theorem fixedSubspace_eq_span {ι : Type w} [Fintype ι] (sigma : K ≃+* K)
    (T : V ≃+ V) (hsemi : ∀ a x, T (a • x) = sigma a • T x)
    (e : Module.Basis ι K V) (he : ∀ i, T (e i) = e i) :
    fixedSubspace sigma T hsemi = Submodule.span (fixedSubfield K sigma) (Set.range e) := by
  apply le_antisymm
  · intro x hx
    apply (e.mem_span_iff_repr_mem (fixedSubfield K sigma) x).mpr
    intro i
    refine ⟨⟨e.repr x i, (mem_fixedSubfield K sigma _).mpr
      (fixed_basis_repr_fixed sigma T hsemi e he x hx i)⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact he i

@[expose] def fixedSpaceBasisOf {ι : Type w} [Fintype ι] (sigma : K ≃+* K)
    (T : V ≃+ V) (hsemi : ∀ a x, T (a • x) = sigma a • T x)
    (e : Module.Basis ι K V) (he : ∀ i, T (e i) = e i) :
    Module.Basis ι (fixedSubfield K sigma) (fixedSubspace sigma T hsemi) :=
  (e.restrictScalars (fixedSubfield K sigma)).map
    (LinearEquiv.ofEq _ _ (fixedSubspace_eq_span sigma T hsemi e he).symm)

theorem fixedSpaceBasisOf_apply {ι : Type w} [Fintype ι] (sigma : K ≃+* K)
    (T : V ≃+ V) (hsemi : ∀ a x, T (a • x) = sigma a • T x)
    (e : Module.Basis ι K V) (he : ∀ i, T (e i) = e i) (i : ι) :
    (fixedSpaceBasisOf sigma T hsemi e he i : V) = e i := by
  simp only [fixedSpaceBasisOf, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.restrictScalars_apply]

theorem exists_fixedSpace_basis [Module.Finite K V] (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
    (T : V ≃+ V) (hT : Function.Involutive T)
    (hsemi : ∀ a x, T (a • x) = sigma a • T x) :
    ∃ e : Module.Basis (Fin (Module.finrank K V)) K V,
      ∃ d : Module.Basis (Fin (Module.finrank K V)) (fixedSubfield K sigma)
        (fixedSubspace sigma T hsemi), ∀ i, (d i : V) = e i ∧ T (e i) = e i := by
  obtain ⟨e, he⟩ := CatalogueBLinearDescent.exists_fixed_finrank_basis
    sigma hsigma hne h2 T hT hsemi
  exact ⟨e, fixedSpaceBasisOf sigma T hsemi e he,
    fun i => ⟨fixedSpaceBasisOf_apply sigma T hsemi e he i, he i⟩⟩

theorem fixedSubspace_finrank [Module.Finite K V] (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
    (T : V ≃+ V) (hT : Function.Involutive T)
    (hsemi : ∀ a x, T (a • x) = sigma a • T x) :
    Module.finrank (fixedSubfield K sigma) (fixedSubspace sigma T hsemi) =
      Module.finrank K V := by
  obtain ⟨e, d, hd⟩ := exists_fixedSpace_basis sigma hsigma hne h2 T hT hsemi
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis d

theorem exists_scalarExtensionEquiv [Module.Finite K V] (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
    (T : V ≃+ V) (hT : Function.Involutive T)
    (hsemi : ∀ a x, T (a • x) = sigma a • T x) :
    ∃ j : (K ⊗[fixedSubfield K sigma] (fixedSubspace sigma T hsemi)) ≃ₗ[K] V,
      ∀ (a : K) (x : fixedSubspace sigma T hsemi), j (a ⊗ₜ x) = a • (x : V) := by
  classical
  obtain ⟨e, d, hd⟩ := exists_fixedSpace_basis sigma hsigma hne h2 T hT hsemi
  let j := (d.baseChange K).equiv e (Equiv.refl _)
  refine ⟨j, ?_⟩
  intro a x
  have hcoeff (i : Fin (Module.finrank K V)) :
      algebraMap (fixedSubfield K sigma) K (d.repr x i) = e.repr (x : V) i := by
    have h := congrArg (fun v : fixedSubspace sigma T hsemi => (v : V)) (d.sum_repr x)
    simp only [Submodule.coe_sum, Submodule.coe_smul, (hd _).1] at h
    change (∑ j, algebraMap (fixedSubfield K sigma) K (d.repr x j) • e j) = (x : V) at h
    have h' := congrArg (fun v => e.repr v i) h
    rw [congrFun (e.repr_sum_self _) i] at h'
    exact h'
  apply e.ext_elem
  intro i
  have hj : e.repr (j (a ⊗ₜ x)) = (d.baseChange K).repr (a ⊗ₜ x) := by
    simp only [j, Module.Basis.equiv, Equiv.refl_symm, Module.Basis.reindex_refl,
      LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [hj, Module.Basis.baseChange_repr_tmul, map_smul, Finsupp.smul_apply]
  change algebraMap (fixedSubfield K sigma) K (d.repr x i) * a = a * e.repr (x : V) i
  rw [hcoeff, mul_comm]

end CFSG.ComponentClassification.CatalogueBOrthogonalDescent
