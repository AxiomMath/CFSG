module

public import CFSG.LieType.Chevalley.FoldedWeylData

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley Matrix
open scoped RealInnerProductSpace

@[expose] def realSymmetrizedCartan (τ : Tag) : Matrix (Fin τ.rank) (Fin τ.rank) ℝ :=
  τ.symmetrizedCartan.map (Int.cast : ℤ → ℝ)

theorem posDef_realSymmetrizedCartan
    (τ : Tag) : (realSymmetrizedCartan τ).PosDef :=
  posDef_symmetrizedCartan τ

structure RootWeightSpace (τ : Tag) where
  ofPi ::
  toPi : Fin τ.rank → ℝ

namespace RootWeightSpace

variable {τ : Tag}

attribute [coe] toPi

instance instCoeFun : CoeFun (RootWeightSpace τ) (fun _ => Fin τ.rank → ℝ) :=
  ⟨toPi⟩

@[ext] theorem ext {x y : RootWeightSpace τ} (h : ∀ i, x i = y i) : x = y := by
  cases x
  cases y
  congr
  exact funext h

variable (τ) in
@[expose] def equivPi : RootWeightSpace τ ≃ (Fin τ.rank → ℝ) :=
  ⟨toPi, ofPi, fun _ => rfl, fun _ => rfl⟩

instance instAddCommGroup : AddCommGroup (RootWeightSpace τ) :=
  (equivPi τ).addCommGroup

@[simp] theorem toPi_zero : (0 : RootWeightSpace τ).toPi = 0 :=
  rfl

@[simp] theorem toPi_add (x y : RootWeightSpace τ) : (x + y).toPi = x.toPi + y.toPi :=
  rfl

@[simp] theorem toPi_neg (x : RootWeightSpace τ) : (-x).toPi = -x.toPi :=
  rfl

@[simp] theorem toPi_sub (x y : RootWeightSpace τ) : (x - y).toPi = x.toPi - y.toPi :=
  rfl

variable (τ) in
@[expose] def addEquivPi : RootWeightSpace τ ≃+ (Fin τ.rank → ℝ) :=
  { equivPi τ with map_add' := fun _ _ => rfl }

instance instModule : Module ℝ (RootWeightSpace τ) :=
  AddEquiv.module ℝ (addEquivPi τ)

@[simp] theorem toPi_smul (c : ℝ) (x : RootWeightSpace τ) : (c • x).toPi = c • x.toPi :=
  rfl

@[simp] theorem toPi_ofPi (v : Fin τ.rank → ℝ) : (ofPi v : RootWeightSpace τ).toPi = v :=
  rfl

variable (τ) in
@[expose] def linearEquivPi : RootWeightSpace τ ≃ₗ[ℝ] (Fin τ.rank → ℝ) where
  toFun := toPi
  invFun := ofPi
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable (τ) in
@[expose, instance_reducible] def core
    : InnerProductSpace.Core ℝ (RootWeightSpace τ) where
  inner x y := x.toPi ⬝ᵥ (realSymmetrizedCartan τ *ᵥ y.toPi)
  conj_inner_symm x y := by
    simp only [conj_trivial]
    rw [dotProduct_mulVec, ← mulVec_transpose, ← conjTranspose_eq_transpose_of_trivial,
      (posDef_realSymmetrizedCartan τ).isHermitian.eq, dotProduct_comm]
  re_inner_nonneg x := by
    simpa using (posDef_realSymmetrizedCartan τ).posSemidef.dotProduct_mulVec_nonneg x.toPi
  add_left x y z := add_dotProduct _ _ _
  smul_left x y r := smul_dotProduct r x.toPi _
  definite x hx := by
    by_contra h
    have h' : x.toPi ≠ 0 := fun h0 => h (by ext i; simp [h0])
    have := (posDef_realSymmetrizedCartan τ).dotProduct_mulVec_pos h'
    rw [star_trivial] at this
    exact this.ne' hx

instance instNormedAddCommGroup : NormedAddCommGroup (RootWeightSpace τ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ _ _ _ _ (core τ)

instance instInnerProductSpace : InnerProductSpace ℝ (RootWeightSpace τ) :=
  InnerProductSpace.ofCore (core τ).toCore

instance instFiniteDimensional : FiniteDimensional ℝ (RootWeightSpace τ) :=
  (linearEquivPi τ).symm.finiteDimensional

theorem inner_def
    (x y : RootWeightSpace τ) :
    ⟪x, y⟫ = x.toPi ⬝ᵥ (realSymmetrizedCartan τ *ᵥ y.toPi) :=
  rfl

theorem inner_eq_sum
    (x y : RootWeightSpace τ) :
    ⟪x, y⟫ = ∑ i, ∑ j, x i * (τ.symmetrizedCartan i j : ℝ) * y j := by
  rw [inner_def]
  simp only [dotProduct, mulVec, realSymmetrizedCartan, Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

@[coe, expose] def ofLattice
    (v : Fin τ.rank → ℤ) : RootWeightSpace τ :=
  ofPi fun j => (v j : ℝ)

@[simp] theorem ofLattice_apply
    (v : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    ofLattice v j = (v j : ℝ) :=
  rfl

@[simp] theorem ofLattice_zero
    : ofLattice (0 : Fin τ.rank → ℤ) = 0 := by
  ext j
  simp

@[simp] theorem ofLattice_add
    (u v : Fin τ.rank → ℤ) :
    ofLattice (u + v) = ofLattice u + ofLattice v := by
  ext j
  simp

@[expose] def ofLatticeHom
    : (Fin τ.rank → ℤ) →+ RootWeightSpace τ where
  toFun := ofLattice
  map_zero' := ofLattice_zero
  map_add' := ofLattice_add

theorem ofLattice_sum
    {ι : Type*} (s : Finset ι) (f : ι → Fin τ.rank → ℤ) :
    ofLattice (∑ k ∈ s, f k) = ∑ k ∈ s, ofLattice (f k) :=
  map_sum ofLatticeHom f s

variable (τ) in
@[expose] def toRootSpace
    : RootWeightSpace τ ≃ₗ[ℝ] RootSpace τ :=
  (linearEquivPi τ).trans (RootSpace.linearEquivPi τ).symm

@[simp] theorem toRootSpace_apply
    (x : RootWeightSpace τ) (j : Fin τ.rank) :
    toRootSpace τ x j = x j :=
  rfl

theorem toRootSpace_ofLattice
    (v : Fin τ.rank → ℤ) :
    toRootSpace τ (ofLattice v) = RootSpace.ofLattice v :=
  rfl

theorem exists_inner_toRootSpace
    (τ : Tag) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x y : RootWeightSpace τ,
      ⟪toRootSpace τ x, toRootSpace τ y⟫ = κ * ⟪x, y⟫ := by
  obtain ⟨κ, hκ, h⟩ := RootSpace.exists_inner_eq_smul τ
  refine ⟨κ, hκ, fun x y => ?_⟩
  rw [h, inner_eq_sum]
  rfl

end RootWeightSpace

open RootWeightSpace

variable {τ : Tag}

@[expose] def realExt
    (f : Module.End ℤ (Fin τ.rank → ℤ)) : Module.End ℝ (RootWeightSpace τ) :=
  (toRootSpace τ).symm.toLinearMap ∘ₗ realExtend f ∘ₗ (toRootSpace τ).toLinearMap

theorem toRootSpace_realExt
    (f : Module.End ℤ (Fin τ.rank → ℤ)) (x : RootWeightSpace τ) :
    toRootSpace τ (realExt f x) = realExtend f (toRootSpace τ x) := by
  simp [realExt]

theorem realExt_ofLattice
    (f : Module.End ℤ (Fin τ.rank → ℤ)) (v : Fin τ.rank → ℤ) :
    realExt f (ofLattice v) = ofLattice (f v) := by
  apply (toRootSpace τ).injective
  rw [toRootSpace_realExt, toRootSpace_ofLattice, realExtend_ofLattice, toRootSpace_ofLattice]

theorem realExt_mul
    (f g : Module.End ℤ (Fin τ.rank → ℤ)) :
    realExt (f * g) = realExt f * realExt g := by
  refine LinearMap.ext fun x => (toRootSpace τ).injective ?_
  rw [Module.End.mul_apply, toRootSpace_realExt, toRootSpace_realExt, toRootSpace_realExt,
    realExtend_mul, Module.End.mul_apply]

theorem realExt_apply
    (f : Module.End ℤ (Fin τ.rank → ℤ)) (x : RootWeightSpace τ) :
    realExt f x = ∑ k, x k • ofLattice (f (Pi.single k 1)) := by
  apply (toRootSpace τ).injective
  rw [toRootSpace_realExt, realExtend_apply, map_sum]
  simp only [map_smul, toRootSpace_ofLattice]
  rfl

theorem realExt_apply_apply
    (f : Module.End ℤ (Fin τ.rank → ℤ)) (x : RootWeightSpace τ)
    (j : Fin τ.rank) : realExt f x j = ∑ k, x k * (f (Pi.single k 1) j : ℝ) := by
  change (realExtend f (toRootSpace τ x)).toPi j = _
  rw [realExtend_apply, RootSpace.toPi_sum, Finset.sum_apply]
  simp [RootSpace.ofLattice_apply]

theorem inner_weylAct_toRootSpace
    (w : WeylGroup τ) (x y : RootWeightSpace τ) :
    ⟪(toRootSpace τ).symm (weylAct τ w (toRootSpace τ x)),
      (toRootSpace τ).symm (weylAct τ w (toRootSpace τ y))⟫ = ⟪x, y⟫ := by
  obtain ⟨κ, hκ, h⟩ := exists_inner_toRootSpace τ
  have e := h ((toRootSpace τ).symm (weylAct τ w (toRootSpace τ x)))
    ((toRootSpace τ).symm (weylAct τ w (toRootSpace τ y)))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearIsometryEquiv.inner_map_map, h] at e
  exact (mul_left_cancel₀ hκ.ne' e).symm

variable (τ) in
@[expose] def weylIsometry
    : WeylGroup τ →* (RootWeightSpace τ ≃ₗᵢ[ℝ] RootWeightSpace τ) where
  toFun w := LinearEquiv.isometryOfInner
    (((toRootSpace τ).trans (weylAct τ w).toLinearEquiv).trans (toRootSpace τ).symm)
    (inner_weylAct_toRootSpace w)
  map_one' := LinearIsometryEquiv.ext fun x => by
    change (toRootSpace τ).symm (weylAct τ 1 (toRootSpace τ x)) = x
    rw [map_one, LinearIsometryEquiv.coe_one, id, LinearEquiv.symm_apply_apply]
  map_mul' w w' := LinearIsometryEquiv.ext fun x => by
    change (toRootSpace τ).symm (weylAct τ (w * w') (toRootSpace τ x)) =
      (toRootSpace τ).symm (weylAct τ w (toRootSpace τ
        ((toRootSpace τ).symm (weylAct τ w' (toRootSpace τ x)))))
    rw [LinearEquiv.apply_symm_apply, weylAct_mul_apply]

theorem weylIsometry_apply
    (w : WeylGroup τ) (x : RootWeightSpace τ) :
    weylIsometry τ w x = (toRootSpace τ).symm (weylAct τ w (toRootSpace τ x)) :=
  rfl

theorem toRootSpace_weylIsometry
    (w : WeylGroup τ) (x : RootWeightSpace τ) :
    toRootSpace τ (weylIsometry τ w x) = weylAct τ w (toRootSpace τ x) := by
  rw [weylIsometry_apply, LinearEquiv.apply_symm_apply]

theorem weylIsometry_eq_realExt
    (w : WeylGroup τ) (x : RootWeightSpace τ) :
    weylIsometry τ w x = realExt (RootSystem.weylAction (isFiniteType_cartan τ) w) x := by
  apply (toRootSpace τ).injective
  rw [toRootSpace_weylIsometry, toRootSpace_realExt, weylAct_apply]
  rfl

theorem weylIsometry_ofLattice
    (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    weylIsometry τ w (ofLattice v) = ofLattice (w • v) := by
  rw [weylIsometry_eq_realExt, realExt_ofLattice]
  rfl

@[expose] def permLatticeLinear {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) :
    Module.End ℤ (Fin τ.rank → ℤ) :=
  LinearMap.funLeft ℤ ℤ π.symm

theorem permLatticeLinear_apply (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    permLatticeLinear π v = permLattice π v :=
  rfl

@[expose] def twistFixedSpace
    (t : TwistTag) : Submodule ℝ (RootWeightSpace t.tag) :=
  LinearMap.eqLocus (realExt (permLatticeLinear t.perm)) LinearMap.id

theorem realExt_permLatticeLinear_apply
    (π : Equiv.Perm (Fin τ.rank)) (x : RootWeightSpace τ)
    (j : Fin τ.rank) : realExt (permLatticeLinear π) x j = x (π.symm j) := by
  rw [realExt_apply_apply]
  simp only [permLatticeLinear_apply, permLattice_single]
  rw [Finset.sum_eq_single (π.symm j)]
  · simp
  · intro k _ hk
    have : π k ≠ j := fun h => hk (by rw [← h, Equiv.symm_apply_apply])
    simp [Ne.symm this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mem_twistFixedSpace_iff
    {t : TwistTag} {x : RootWeightSpace t.tag} :
    x ∈ twistFixedSpace t ↔ ∀ i, x (t.perm i) = x i := by
  change realExt (permLatticeLinear t.perm) x = x ↔ _
  constructor
  · intro h i
    have := congrArg (fun y : RootWeightSpace t.tag => y (t.perm i)) h
    simp only [realExt_permLatticeLinear_apply, Equiv.symm_apply_apply] at this
    exact this.symm
  · intro h
    ext j
    rw [realExt_permLatticeLinear_apply]
    simpa using (h (t.perm.symm j)).symm

theorem weylIsometry_comm_realExt_perm
    {t : TwistTag} {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) (x : RootWeightSpace t.tag) :
    weylIsometry t.tag w (realExt (permLatticeLinear t.perm) x) =
      realExt (permLatticeLinear t.perm) (weylIsometry t.tag w x) := by
  have hWP : RootSystem.weylAction (isFiniteType_cartan t.tag) w * permLatticeLinear t.perm =
      permLatticeLinear t.perm * RootSystem.weylAction (isFiniteType_cartan t.tag) w := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, permLatticeLinear_apply,
      permLatticeLinear_apply]
    exact (mem_relWeylTwist_iff_smul t).1 hw v
  rw [weylIsometry_eq_realExt, weylIsometry_eq_realExt, ← Module.End.mul_apply, ← realExt_mul,
    hWP, realExt_mul, Module.End.mul_apply]

theorem weylIsometry_mem_twistFixedSpace
    {t : TwistTag} {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) {x : RootWeightSpace t.tag} (hx : x ∈ twistFixedSpace t) :
    weylIsometry t.tag w x ∈ twistFixedSpace t := by
  change realExt (permLatticeLinear t.perm) (weylIsometry t.tag w x) = weylIsometry t.tag w x
  rw [← weylIsometry_comm_realExt_perm hw]
  exact congrArg (weylIsometry t.tag w) hx

theorem ofLattice_mem_twistFixedSpace
    {t : TwistTag} {v : Fin t.tag.rank → ℤ}
    (hv : v ∈ t.fixedLattice) : ofLattice v ∈ twistFixedSpace t := by
  rw [mem_twistFixedSpace_iff]
  intro i
  simp only [ofLattice_apply]
  exact_mod_cast (t.mem_fixedLattice_iff_forall).1 hv i

end CFSG.LieType.Chevalley
