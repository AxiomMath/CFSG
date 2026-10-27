module

public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsBlocks

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

open Module Matrix CFSG.ProperTwoGeneratedCore.PairedTensor

section Hom

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def homSpace (τ : Representation (ZMod 2) K W) (i : Fin 4) :
    Submodule (ZMod 2) (labelSub i →ₗ[ZMod 2] W) where
  carrier := {φ | ∀ g x, φ (labelRep i g x) = τ (g, 1) (φ x)}
  add_mem' {φ ψ} hφ hψ g x := by
    rw [LinearMap.add_apply, LinearMap.add_apply, hφ, hψ, map_add]
  zero_mem' g x := by rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  smul_mem' c φ hφ g x := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hφ, map_smul]

@[expose] def homRep (τ : Representation (ZMod 2) K W) (i : Fin 4) :
    Representation (ZMod 2) S (labelSub i →ₗ[ZMod 2] W) where
  toFun h :=
    { toFun := fun φ => τ (1, h) ∘ₗ φ
      map_add' := fun φ ψ => LinearMap.comp_add _ _ _
      map_smul' := fun c φ => LinearMap.comp_smul _ _ _ }
  map_one' := LinearMap.ext fun φ => LinearMap.ext fun x => by
    change τ (1, 1) (φ x) = φ x
    rw [show ((1, 1) : K) = 1 from rfl, map_one, Module.End.one_apply]
  map_mul' h h' := LinearMap.ext fun φ => LinearMap.ext fun x => by
    change τ (1, h * h') (φ x) = τ (1, h) (τ (1, h') (φ x))
    rw [show ((1, h * h') : K) = (1, h) * (1, h') by rw [Prod.mk_mul_mk, one_mul], map_mul,
      Module.End.mul_apply]

theorem homRep_apply (τ : Representation (ZMod 2) K W) (i : Fin 4) (h : S)
    (φ : labelSub i →ₗ[ZMod 2] W) (x : labelSub i) : homRep τ i h φ x = τ (1, h) (φ x) :=
  rfl

theorem rep_one_mul (τ : Representation (ZMod 2) K W) (g h : S) (v : W) :
    τ (1, h) (τ (g, 1) v) = τ (g, h) v := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

theorem rep_mul_one (τ : Representation (ZMod 2) K W) (g h : S) (v : W) :
    τ (g, 1) (τ (1, h) v) = τ (g, h) v := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

theorem isInv_homSpace (τ : Representation (ZMod 2) K W) (i : Fin 4) :
    IsInv (homRep τ i) (homSpace τ i) := by
  intro h φ hφ g x
  rw [homRep_apply, homRep_apply, hφ, rep_one_mul, rep_mul_one]

theorem lift_flip_outer (τ : Representation (ZMod 2) K W) (i j : Fin 4)
    (B : labelSub j →ₗ[ZMod 2] labelSub i →ₗ[ZMod 2] W) (hB : ∀ y, B y ∈ homSpace τ i)
    (hBeq : ∀ h y, B (labelRep j h y) = homRep τ i h (B y)) (k : K)
    (m : TensorProduct (ZMod 2) (labelSub i) (labelSub j)) :
    TensorProduct.lift B.flip (outer (labelRep i) (labelRep j) k m) =
      τ k (TensorProduct.lift B.flip m) := by
  induction m with
  | tmul x y =>
    rw [outer_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul, LinearMap.flip_apply,
      LinearMap.flip_apply, hBeq, homRep_apply, hB y k.1 x, rep_one_mul]
  | add m m' h h' => simp only [map_add, h, h']

end Hom

theorem exists_equiv_blockRepK {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) K W) (hτ : τ.IsIrreducible) :
    ∃ ij, Nonempty (τ.Equiv (blockRepK ij)) := by
  have hnt := ((isIrreducible_iff τ).1 hτ).1
  let τ₁ := τ.comp (MonoidHom.inl S S)
  obtain ⟨U, -, hU, hU0, hUmin⟩ := exists_minimal τ₁ (U₀ := ⊤) (fun _ _ _ => Submodule.mem_top)
    top_ne_bot
  obtain ⟨i, ⟨e₁⟩⟩ := exists_equiv_labelRep _ (isIrreducible_subrepOf hU hU0 hUmin)
  let φ₀ : labelSub i →ₗ[ZMod 2] W := U.subtype ∘ₗ e₁.symm.toLinearEquiv.toLinearMap
  have hφ₀ : φ₀ ∈ homSpace τ i := fun g x => by
    change ((e₁.symm (labelRep i g x) : U) : W) = τ (g, 1) ((e₁.symm x : U) : W)
    rw [Equiv.map_apply e₁.symm g x]
    rfl
  have hφ₀0 : φ₀ ≠ 0 := by
    have := (labelRep_absIrr i).1
    obtain ⟨x, hx⟩ := exists_ne (0 : labelSub i)
    intro h
    have h1 := LinearMap.congr_fun h x
    change ((e₁.symm x : U) : W) = 0 at h1
    exact hx (e₁.symm.toLinearEquiv.map_eq_zero_iff.1 (Subtype.ext h1))
  have hH0 : homSpace τ i ≠ ⊥ := fun h => hφ₀0 (by
    have h1 : φ₀ ∈ (⊥ : Submodule (ZMod 2) (labelSub i →ₗ[ZMod 2] W)) := h ▸ hφ₀
    exact (Submodule.mem_bot _).1 h1)
  obtain ⟨Y, hYH, hY, hY0, hYmin⟩ := exists_minimal (homRep τ i) (isInv_homSpace τ i) hH0
  obtain ⟨j, ⟨e₂⟩⟩ := exists_equiv_labelRep _ (isIrreducible_subrepOf hY hY0 hYmin)
  let B : labelSub j →ₗ[ZMod 2] labelSub i →ₗ[ZMod 2] W :=
    Y.subtype ∘ₗ e₂.symm.toLinearEquiv.toLinearMap
  let ev : TensorProduct (ZMod 2) (labelSub i) (labelSub j) →ₗ[ZMod 2] W :=
    TensorProduct.lift B.flip
  have hev : ∀ x y, ev (x ⊗ₜ y) = ((e₂.symm y : Y) : labelSub i →ₗ[ZMod 2] W) x := fun x y => rfl
  have hevK : ∀ (k : K) m, ev (outer (labelRep i) (labelRep j) k m) = τ k (ev m) :=
    lift_flip_outer τ i j B (fun y => hYH (e₂.symm y).2) (fun h y => by
      change ((e₂.symm (labelRep j h y) : Y) : labelSub i →ₗ[ZMod 2] W) = _
      rw [Equiv.map_apply e₂.symm h y]
      rfl)
  have hev0 : ev ≠ 0 := by
    have := (labelRep_absIrr j).1
    obtain ⟨y, hy⟩ := exists_ne (0 : labelSub j)
    have hψ : ((e₂.symm y : Y) : labelSub i →ₗ[ZMod 2] W) ≠ 0 := fun h =>
      hy (e₂.symm.toLinearEquiv.map_eq_zero_iff.1 (Subtype.ext h))
    obtain ⟨x, hx⟩ : ∃ x, ((e₂.symm y : Y) : labelSub i →ₗ[ZMod 2] W) x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hψ (LinearMap.ext hcon)
    intro h
    exact hx ((hev x y).symm.trans (LinearMap.congr_fun h _))
  obtain ⟨e⟩ := CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.nonempty_equiv_of_ne_zero hτ
    ((labelRep_absIrr i).outer (labelRep_absIrr j)).isIrreducible ev hevK hev0
  exact ⟨(i, j), ⟨e.trans (blockEquiv (i, j))⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits
