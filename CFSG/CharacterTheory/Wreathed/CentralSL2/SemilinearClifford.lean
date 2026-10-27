module

public import CFSG.CharacterTheory.Wreathed.AbelianInertiaInduction
public import CFSG.CharacterTheory.Wreathed.CentralSL2.Basic

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

noncomputable instance fieldSubgroup_fintype {F : Type} [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) : Fintype Sigma :=
  Fintype.ofFinite _

section Layer

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def baseLayer :
    Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
  (SemidirectProduct.inl : CentralExtension F b m hm heven →*
    SemilinearExtension F b m hm heven Sigma hSigma).range

instance baseLayer_normal : (baseLayer F b m hm heven Sigma hSigma).Normal := by
  rw [baseLayer, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

variable {F b m hm heven Sigma hSigma}

theorem mem_baseLayer_iff (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    h ∈ baseLayer F b m hm heven Sigma hSigma ↔ h.right = 1 := by
  rw [baseLayer, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  rfl

theorem inl_mem_baseLayer (g : CentralExtension F b m hm heven) :
    (SemidirectProduct.inl g : SemilinearExtension F b m hm heven Sigma hSigma) ∈
      baseLayer F b m hm heven Sigma hSigma :=
  ⟨g, rfl⟩

theorem eq_inl_left_of_mem_baseLayer {h : SemilinearExtension F b m hm heven Sigma hSigma}
    (hh : h ∈ baseLayer F b m hm heven Sigma hSigma) : SemidirectProduct.inl h.left = h := by
  obtain ⟨g, rfl⟩ := hh
  rfl

@[expose] noncomputable def baseLayerEquiv :
    CentralExtension F b m hm heven ≃* baseLayer F b m hm heven Sigma hSigma :=
  MonoidHom.ofInjective SemidirectProduct.inl_injective

theorem baseLayerEquiv_apply (g : CentralExtension F b m hm heven) :
    ((baseLayerEquiv (Sigma := Sigma) (hSigma := hSigma) g : baseLayer F b m hm heven Sigma
      hSigma) : SemilinearExtension F b m hm heven Sigma hSigma) = SemidirectProduct.inl g := rfl

theorem baseLayerEquiv_symm_apply (n : baseLayer F b m hm heven Sigma hSigma) :
    baseLayerEquiv.symm n = (n : SemilinearExtension F b m hm heven Sigma hSigma).left := by
  apply baseLayerEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [baseLayerEquiv_apply, eq_inl_left_of_mem_baseLayer n.2]

@[expose] noncomputable def layerFunction (θ : CentralExtension F b m hm heven → ℂ) :
    baseLayer F b m hm heven Sigma hSigma → ℂ :=
  fun n => θ (n : SemilinearExtension F b m hm heven Sigma hSigma).left

theorem layerFunction_eq (θ : CentralExtension F b m hm heven → ℂ) :
    layerFunction (Sigma := Sigma) (hSigma := hSigma) θ = θ ∘ baseLayerEquiv.symm := by
  funext n
  rw [Function.comp_apply, baseLayerEquiv_symm_apply]
  rfl

theorem layerFunction_injective :
    Function.Injective (layerFunction (F := F) (b := b) (m := m) (hm := hm) (heven := heven)
      (Sigma := Sigma) (hSigma := hSigma)) := by
  intro θ θ' h
  funext g
  exact congrFun h (baseLayerEquiv g)

theorem restrict_baseLayer_eq (χ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ) :
    (fun n : baseLayer F b m hm heven Sigma hSigma => χ n) =
      layerFunction fun g => χ (SemidirectProduct.inl g) := by
  funext n
  change χ n = χ (SemidirectProduct.inl (n : SemilinearExtension F b m hm heven Sigma hSigma).left)
  rw [eq_inl_left_of_mem_baseLayer n.2]

theorem layerFunction_mem_blocksIrr {θ : CentralExtension F b m hm heven → ℂ}
    (hθ : θ ∈ BlocksIrr (CentralExtension F b m hm heven)) :
    layerFunction (Sigma := Sigma) (hSigma := hSigma) θ ∈
      BlocksIrr (baseLayer F b m hm heven Sigma hSigma) := by
  rw [layerFunction_eq]
  obtain ⟨W, i₁, i₂, i₃, τ, hτ, rfl⟩ := hθ
  exact ⟨W, i₁, i₂, i₃, τ.comp baseLayerEquiv.symm.toMonoidHom,
    CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective _ baseLayerEquiv.symm.surjective τ hτ,
    rfl⟩

theorem blocksInnerProduct_layerFunction [Finite F] (θ θ' : CentralExtension F b m hm heven → ℂ) :
    BlocksInnerProduct (layerFunction (Sigma := Sigma) (hSigma := hSigma) θ) (layerFunction θ') =
      BlocksInnerProduct θ θ' := by
  have : Fintype F := Fintype.ofFinite F
  unfold BlocksInnerProduct
  rw [Nat.card_congr (baseLayerEquiv (Sigma := Sigma) (hSigma := hSigma)).toEquiv.symm]
  congr 1
  refine Fintype.sum_equiv (baseLayerEquiv (Sigma := Sigma) (hSigma := hSigma)).toEquiv.symm _ _
    fun n => ?_
  rw [layerFunction_eq, layerFunction_eq]
  rfl

end Layer

section Twist

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def fieldTwist (σ : Sigma)
    (θ : CentralExtension F b m hm heven → ℂ) : CentralExtension F b m hm heven → ℂ :=
  fun g => θ (fieldAction F b m hm heven Sigma hSigma σ⁻¹ g)

theorem fieldTwist_apply (σ : Sigma) (θ : CentralExtension F b m hm heven → ℂ)
    (g : CentralExtension F b m hm heven) :
    fieldTwist hSigma σ θ g = θ (fieldAction F b m hm heven Sigma hSigma σ⁻¹ g) := rfl

theorem fieldTwist_one (θ : CentralExtension F b m hm heven → ℂ) :
    fieldTwist hSigma 1 θ = θ := by
  funext g
  rw [fieldTwist_apply, inv_one, map_one, MulAut.one_apply]

theorem fieldTwist_mul (σ τ : Sigma) (θ : CentralExtension F b m hm heven → ℂ) :
    fieldTwist hSigma (σ * τ) θ = fieldTwist hSigma σ (fieldTwist hSigma τ θ) := by
  funext g
  rw [fieldTwist_apply, fieldTwist_apply, fieldTwist_apply, _root_.mul_inv_rev, map_mul,
    MulAut.mul_apply]

@[expose] noncomputable def twistStabilizer
    (θ : CentralExtension F b m hm heven → ℂ) : Subgroup Sigma where
  carrier := {σ | fieldTwist hSigma σ θ = θ}
  one_mem' := fieldTwist_one hSigma θ
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_ofPred_eq] at hσ hτ ⊢
    rw [fieldTwist_mul hSigma, hτ, hσ]
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_ofPred_eq] at hσ ⊢
    have h1 := fieldTwist_mul hSigma σ⁻¹ σ θ
    rw [inv_mul_cancel, fieldTwist_one hSigma, hσ] at h1
    exact h1.symm

theorem mem_twistStabilizer_iff (θ : CentralExtension F b m hm heven → ℂ) (σ : Sigma) :
    σ ∈ twistStabilizer hSigma θ ↔ fieldTwist hSigma σ θ = θ := Iff.rfl

theorem conj_inl_left (h : SemilinearExtension F b m hm heven Sigma hSigma)
    (g : CentralExtension F b m hm heven) :
    (h⁻¹ * SemidirectProduct.inl g * h).left =
      fieldAction F b m hm heven Sigma hSigma h.right⁻¹ (h.left⁻¹ * g * h.left) := by
  simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.left_inl,
    SemidirectProduct.mul_right, SemidirectProduct.inv_right, SemidirectProduct.right_inl,
    mul_one, map_mul, map_inv]

theorem conjugateNormalCharacter_layer {θ : CentralExtension F b m hm heven → ℂ}
    (hθ : BlocksIsClassFunction θ) (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    conjugateNormalCharacter (baseLayer F b m hm heven Sigma hSigma) (layerFunction θ) h =
      layerFunction (fieldTwist hSigma h.right θ) := by
  funext n
  rw [conjugateNormalCharacter_apply]
  change θ (h⁻¹ * (n : SemilinearExtension F b m hm heven Sigma hSigma) * h).left =
    θ (fieldAction F b m hm heven Sigma hSigma h.right⁻¹
      (n : SemilinearExtension F b m hm heven Sigma hSigma).left)
  conv_lhs => rw [← eq_inl_left_of_mem_baseLayer n.2]
  rw [conj_inl_left hSigma, map_mul, map_mul, map_inv]
  have h1 := hθ (fieldAction F b m hm heven Sigma hSigma h.right⁻¹
      (n : SemilinearExtension F b m hm heven Sigma hSigma).left)
    (fieldAction F b m hm heven Sigma hSigma h.right⁻¹ h.left)⁻¹
  rw [inv_inv] at h1
  exact h1

theorem characterInertiaSubgroup_layer {θ : CentralExtension F b m hm heven → ℂ}
    (hθ : BlocksIsClassFunction θ) :
    characterInertiaSubgroup (baseLayer F b m hm heven Sigma hSigma) (layerFunction θ) =
      (twistStabilizer hSigma θ).comap SemidirectProduct.rightHom := by
  ext h
  rw [mem_characterInertiaSubgroup_iff, conjugateNormalCharacter_layer hSigma hθ,
    Subgroup.mem_comap,
    mem_twistStabilizer_iff]
  exact layerFunction_injective.eq_iff

end Twist

section Quotient

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem quotient_baseLayer_isMulCommutative [Finite F]
    (I : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)) :
    IsMulCommutative (I ⧸ (baseLayer F b m hm heven Sigma hSigma).subgroupOf I) := by
  have hcyc : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
  have hcomm : ∀ x y : Sigma, x * y = y * x := fun x y => IsCyclic.commGroup.mul_comm x y
  refine ⟨⟨fun a c => ?_⟩⟩
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
        mem_baseLayer_iff]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_right,
        SemidirectProduct.inv_right, _root_.mul_inv_rev]
      rw [hcomm ((y : SemilinearExtension F b m hm heven Sigma hSigma).right)
        ((x : SemilinearExtension F b m hm heven Sigma hSigma).right)]
      group

@[expose] noncomputable def semilinearInertia (S : Subgroup Sigma) :
    Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
  S.comap SemidirectProduct.rightHom

theorem mem_semilinearInertia_iff (S : Subgroup Sigma)
    (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    h ∈ semilinearInertia S ↔ h.right ∈ S := Iff.rfl

theorem baseLayer_le_semilinearInertia (S : Subgroup Sigma) :
    baseLayer F b m hm heven Sigma hSigma ≤ semilinearInertia S := by
  intro h hh
  rw [mem_semilinearInertia_iff, (mem_baseLayer_iff h).mp hh]
  exact S.one_mem

@[expose] noncomputable def inertiaQuotientEquiv (S : Subgroup Sigma) :
    (semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S ⧸
      (baseLayer F b m hm heven Sigma hSigma).subgroupOf (semilinearInertia S)) ≃* S := by
  refine QuotientGroup.quotientMulEquivOfEq (M := (baseLayer F b m hm heven Sigma
    hSigma).subgroupOf (semilinearInertia S)) ?_ |>.trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((SemidirectProduct.rightHom.comp (semilinearInertia S).subtype).codRestrict
        S fun x => x.2) ?_)
  · ext x
    rw [Subgroup.mem_subgroupOf, mem_baseLayer_iff, MonoidHom.mem_ker]
    constructor
    · intro hx
      apply Subtype.ext
      exact hx
    · intro hx
      exact congrArg Subtype.val hx
  · intro σ
    refine ⟨⟨SemidirectProduct.inr (σ : Sigma), ?_⟩, ?_⟩
    · rw [mem_semilinearInertia_iff, SemidirectProduct.right_inr]
      exact σ.2
    · rfl

theorem inertiaQuotientEquiv_mk (S : Subgroup Sigma)
    (x : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
    (inertiaQuotientEquiv S (x : semilinearInertia (hm := hm) (heven := heven)
      (hSigma := hSigma) S ⧸ (baseLayer F b m hm heven Sigma hSigma).subgroupOf
        (semilinearInertia S)) : Sigma) =
        (x : SemilinearExtension F b m hm heven Sigma hSigma).right := rfl

end Quotient

end CFSG.Wreathed.CentralSL2
