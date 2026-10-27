module

public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.CartanPositiveForm
public import TauCeti.GroupTheory.Coxeter.Geometric

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem

variable (τ : Tag)

@[expose] def reflectUnit
    (i : Fin τ.rank) : (Module.End ℤ (Fin τ.rank → ℤ))ˣ where
  val := (reflectHom τ i).toIntLinearMap
  inv := (reflectHom τ i).toIntLinearMap
  val_inv := LinearMap.ext fun v => reflect_reflect τ i v
  inv_val := LinearMap.ext fun v => reflect_reflect τ i v

theorem reflectUnit_apply (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    (reflectUnit τ i : Module.End ℤ (Fin τ.rank → ℤ)) v = reflect τ i v :=
  rfl

@[expose] def latticeWeylGroup
    : Subgroup (Module.End ℤ (Fin τ.rank → ℤ))ˣ :=
  Subgroup.closure (Set.range (reflectUnit τ))

@[expose] def latticeSimple (i : Fin τ.rank) : latticeWeylGroup τ :=
  ⟨reflectUnit τ i, Subgroup.subset_closure ⟨i, rfl⟩⟩

@[expose] def weylToAut
    : WeylGroup τ →* (Module.End ℤ (Fin τ.rank → ℤ))ˣ :=
  (weylAction (isFiniteType_cartan τ)).toHomUnits

variable {τ}

theorem weylToAut_apply
    (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    (weylToAut τ w : Module.End ℤ (Fin τ.rank → ℤ)) v = w • v :=
  rfl

theorem weylToAut_simple
    (i : Fin τ.rank) : weylToAut τ (simple τ i) = reflectUnit τ i :=
  Units.ext (LinearMap.ext fun v => by rw [weylToAut_apply, simple_smul, reflectUnit_apply])

theorem weylToAut_injective
    : Function.Injective (weylToAut τ) := fun w w' h => by
  apply weylAction_injective (isFiniteType_cartan τ)
  have h' := congrArg (fun u : (Module.End ℤ (Fin τ.rank → ℤ))ˣ =>
    (u : Module.End ℤ (Fin τ.rank → ℤ))) h
  simpa only [weylToAut, MonoidHom.coe_toHomUnits] using h'

theorem range_weylToAut
    : (weylToAut τ).range = latticeWeylGroup τ := by
  rw [MonoidHom.range_eq_map, ← (coxeterSystem τ).subgroup_closure_range_simple,
    MonoidHom.map_closure, ← Set.range_comp,
    show ⇑(weylToAut τ) ∘ (coxeterSystem τ).simple = reflectUnit τ from funext weylToAut_simple]
  rfl

variable (τ) in
@[expose] def weylEquivLattice
    : WeylGroup τ ≃* latticeWeylGroup τ :=
  (MonoidHom.ofInjective (f := weylToAut τ) weylToAut_injective).trans
    (MulEquiv.subgroupCongr range_weylToAut)

theorem weylEquivLattice_apply
    (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    ((weylEquivLattice τ w : (Module.End ℤ (Fin τ.rank → ℤ))ˣ) :
      Module.End ℤ (Fin τ.rank → ℤ)) v = w • v :=
  rfl

theorem weylEquivLattice_simple
    (i : Fin τ.rank) :
    weylEquivLattice τ (simple τ i) = latticeSimple τ i :=
  Subtype.ext (weylToAut_simple i)

variable (τ) in
theorem borel_monomial_data
    (R : Type*) [CommRing R] :
    latticeWeylGroup τ = Subgroup.closure (Set.range (reflectUnit τ)) ∧
    (∀ i v, (reflectUnit τ i : Module.End ℤ (Fin τ.rank → ℤ)) v = reflect τ i v) ∧
    (∃ e : WeylGroup τ ≃* latticeWeylGroup τ, (∀ i, e (simple τ i) = latticeSimple τ i) ∧
      ∀ w v, ((e w : (Module.End ℤ (Fin τ.rank → ℤ))ˣ) : Module.End ℤ (Fin τ.rank → ℤ)) v =
        w • v) ∧
    torusGroup τ R = Subgroup.closure (Set.range fun p : Fin τ.rank × Rˣ => torusElt τ R p.1 p.2) ∧
    monomialSubgroup τ R = Subgroup.closure
      ((torusGroup τ R : Set (Module.End R (RootModule τ R))ˣ) ∪
        Set.range fun i : Fin τ.rank => weylElt τ R i 1) ∧
    borelGroup τ R = Subgroup.closure
      ((torusGroup τ R : Set (Module.End R (RootModule τ R))ˣ) ∪ (posUnipotent τ R : Set _)) ∧
    τ.symmetrizedCartan = τ.symmetrizer * τ.cartan ∧ τ.symmetrizedCartan.IsSymm := by
  refine ⟨rfl, fun i v => rfl, ⟨weylEquivLattice τ, weylEquivLattice_simple, fun w v => rfl⟩,
    rfl, ?_, ?_, rfl, symmetrizedCartan_isSymm τ⟩
  · rw [Subgroup.closure_union, Subgroup.closure_eq]
    rfl
  · rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    rfl

theorem orderOf_simple_eq_two
    (i : Fin τ.rank) : orderOf (simple τ i) = 2 :=
  orderOf_eq_prime ((coxeterSystem τ).simple_sq i) ((coxeterSystem τ).simple_ne_one i)

theorem orderOf_simple_mul_simple_eq
    (i j : Fin τ.rank) :
    orderOf (simple τ i * simple τ j) = TauCeti.coxeterOrder (τ.cartan i j * τ.cartan j i) := by
  rw [(coxeterSystem τ).orderOf_simple_mul_simple i j, coxeterMatrix,
    TauCeti.coxeterMatrixOfCartanMatrix_apply]

variable (τ) in
theorem finite_weyl_pair_orders :
    Finite (latticeWeylGroup τ) ∧
    (∀ g ∈ latticeWeylGroup τ, ∀ v, IsRoot τ v →
      IsRoot τ ((g : Module.End ℤ (Fin τ.rank → ℤ)) v)) ∧
    (∀ g ∈ latticeWeylGroup τ,
      (∀ v, IsRoot τ v → (g : Module.End ℤ (Fin τ.rank → ℤ)) v = v) → g = 1) ∧
    Function.Injective (latticeSimple τ) ∧ (∀ i, orderOf (latticeSimple τ i) = 2) ∧
    ∀ i j : Fin τ.rank, i ≠ j →
      (τ.cartan i j * τ.cartan j i = 0 ∨ τ.cartan i j * τ.cartan j i = 1 ∨
        τ.cartan i j * τ.cartan j i = 2 ∨ τ.cartan i j * τ.cartan j i = 3) ∧
      (τ.cartan i j * τ.cartan j i = 0 → orderOf (latticeSimple τ i * latticeSimple τ j) = 2) ∧
      (τ.cartan i j * τ.cartan j i = 1 → orderOf (latticeSimple τ i * latticeSimple τ j) = 3) ∧
      (τ.cartan i j * τ.cartan j i = 2 → orderOf (latticeSimple τ i * latticeSimple τ j) = 4) ∧
      (τ.cartan i j * τ.cartan j i = 3 → orderOf (latticeSimple τ i * latticeSimple τ j) = 6) := by
  set e := weylEquivLattice τ
  have hsimple : latticeSimple τ = e ∘ simple τ := funext fun i => (weylEquivLattice_simple i).symm
  have hpair : ∀ i j, orderOf (latticeSimple τ i * latticeSimple τ j) =
      TauCeti.coxeterOrder (τ.cartan i j * τ.cartan j i) := fun i j => by
    rw [hsimple, Function.comp_apply, Function.comp_apply, ← map_mul, MulEquiv.orderOf_eq,
      orderOf_simple_mul_simple_eq]
  refine ⟨Finite.of_equiv _ e.toEquiv, fun g hg v hv => ?_, fun g hg hfix => ?_,
    ?_, fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨w, hw⟩ := e.surjective ⟨g, hg⟩
    have h : (g : Module.End ℤ (Fin τ.rank → ℤ)) v = w • v := by
      rw [← weylEquivLattice_apply, hw]
    rw [h]
    exact IsRoot.smul hv w
  · obtain ⟨w, hw⟩ := e.surjective ⟨g, hg⟩
    have h1 : w = 1 := ext_single fun i => by
      rw [one_smul, ← weylEquivLattice_apply, hw]
      exact hfix _ (isRoot_single τ i)
    have h2 := congrArg Subtype.val hw
    rw [h1, map_one] at h2
    exact h2.symm
  · rw [hsimple]
    exact e.injective.comp (coxeterSystem τ).simple_injective
  · rw [hsimple, Function.comp_apply, MulEquiv.orderOf_eq, orderOf_simple_eq_two]
  · have hmem := (isFiniteType_cartan τ).apply_mul_apply_mem_of_ne hij
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    refine ⟨hmem, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      rw [hpair, h] <;> simp

end CFSG.LieType.Chevalley
