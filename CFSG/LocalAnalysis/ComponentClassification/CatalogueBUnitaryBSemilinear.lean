module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBInner

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryB

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CatalogueBFixedCentralQuotient

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

section SemiConj

variable (h : UnitaryFieldData p f E) (τ : V ≃+ V)
  (hτ : ∀ (c : E) (v : V), τ (c • v) = h.bar c • τ v)

include hτ in
theorem symm_map_smul (c : E) (v : V) : τ.symm (c • v) = h.bar c • τ.symm v := by
  apply τ.injective
  rw [AddEquiv.apply_symm_apply, hτ, AddEquiv.apply_symm_apply, h.bar_bar]

@[expose] def semiConjEnd (g : V →ₗ[E] V) : V →ₗ[E] V where
  toFun v := τ (g (τ.symm v))
  map_add' v w := by rw [map_add, map_add, map_add]
  map_smul' c v := by
    rw [symm_map_smul h τ hτ, map_smul, hτ, h.bar_bar, RingHom.id_apply]

theorem semiConjEnd_apply (g : V →ₗ[E] V) (v : V) :
    semiConjEnd h τ hτ g v = τ (g (τ.symm v)) :=
  rfl

@[expose] def semiConjHom : Module.End E V →* Module.End E V where
  toFun := semiConjEnd h τ hτ
  map_one' := LinearMap.ext fun v => τ.apply_symm_apply v
  map_mul' g g' := LinearMap.ext fun v => by
    change τ (g (g' (τ.symm v))) = τ (g (τ.symm (τ (g' (τ.symm v)))))
    rw [AddEquiv.symm_apply_apply]

@[expose] def semiConjGL : MulAut (LinearMap.GeneralLinearGroup E V) where
  toFun := Units.map (semiConjHom h τ hτ)
  invFun := Units.map (semiConjHom h τ.symm (symm_map_smul h τ hτ))
  left_inv g := Units.ext (LinearMap.ext fun v => by
    change τ.symm (τ ((g : V →ₗ[E] V) (τ.symm (τ v)))) = (g : V →ₗ[E] V) v
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply])
  right_inv g := Units.ext (LinearMap.ext fun v => by
    change τ (τ.symm ((g : V →ₗ[E] V) (τ (τ.symm v)))) = (g : V →ₗ[E] V) v
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply])
  map_mul' := map_mul _

theorem coe_semiConjGL (g : LinearMap.GeneralLinearGroup E V) :
    ((semiConjGL h τ hτ g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) =
      semiConjEnd h τ hτ (g : V →ₗ[E] V) :=
  rfl

theorem coe_semiConjGL_symm (g : LinearMap.GeneralLinearGroup E V) :
    (((semiConjGL h τ hτ).symm g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) =
      semiConjEnd h τ.symm (symm_map_smul h τ hτ) (g : V →ₗ[E] V) :=
  rfl

theorem semiConjEnd_smul_one (c : E) :
    semiConjEnd h τ hτ (c • 1) = h.bar c • (1 : Module.End E V) :=
  LinearMap.ext fun v => by
    rw [semiConjEnd_apply, LinearMap.smul_apply, Module.End.one_apply, hτ,
      AddEquiv.apply_symm_apply, LinearMap.smul_apply, Module.End.one_apply]

end SemiConj

section Det

variable (h : UnitaryFieldData p f E)

theorem coordConj_aux {ι : Type*} [Fintype ι] (b : Module.Basis ι E V) (v : V) :
    (b.equivFun.symm fun i => h.bar (b.equivFun (b.equivFun.symm
      fun j => h.bar (b.equivFun v j)) i)) = v := by
  rw [LinearEquiv.apply_symm_apply]
  simp only [h.bar_bar]
  exact b.equivFun.symm_apply_apply v

@[expose] def coordConj {ι : Type*} [Fintype ι] (b : Module.Basis ι E V) : V ≃+ V where
  toFun v := b.equivFun.symm fun i => h.bar (b.equivFun v i)
  invFun v := b.equivFun.symm fun i => h.bar (b.equivFun v i)
  left_inv v := coordConj_aux h b v
  right_inv v := coordConj_aux h b v
  map_add' v w := by
    rw [← map_add]
    congr 1
    funext i
    rw [map_add, Pi.add_apply, map_add, Pi.add_apply]

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι E V)

theorem coordConj_apply (v : V) :
    coordConj h b v = b.equivFun.symm fun i => h.bar (b.equivFun v i) :=
  rfl

theorem coordConj_smul (c : E) (v : V) : coordConj h b (c • v) = h.bar c • coordConj h b v := by
  rw [coordConj_apply, coordConj_apply, ← map_smul]
  congr 1
  funext i
  rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, smul_eq_mul]

theorem coordConj_symm_apply (v : V) : (coordConj h b).symm v = coordConj h b v :=
  rfl

theorem repr_coordConj (v : V) (i : ι) : b.repr (coordConj h b v) i = h.bar (b.repr v i) := by
  rw [← b.equivFun_apply, ← b.equivFun_apply, coordConj_apply, LinearEquiv.apply_symm_apply]

theorem coordConj_basis [DecidableEq ι] (i : ι) : coordConj h b (b i) = b i := by
  rw [coordConj_apply, LinearEquiv.symm_apply_eq]
  funext j
  simp only [b.equivFun_self]
  split_ifs <;> simp

theorem det_semiConjEnd [FiniteDimensional E V] (τ : V ≃+ V)
    (hτ : ∀ (c : E) (v : V), τ (c • v) = h.bar c • τ v) (g : V →ₗ[E] V) :
    LinearMap.det (semiConjEnd h τ hτ g) = h.bar (LinearMap.det g) := by
  classical
  let b := Module.finBasis E V
  let c := coordConj h b
  have hc : ∀ (a : E) (v : V), c (a • v) = h.bar a • c v := coordConj_smul h b
  let L : V ≃ₗ[E] V :=
    { toFun := fun v => τ (c v)
      invFun := fun v => c.symm (τ.symm v)
      map_add' := fun v w => by rw [map_add, map_add]
      map_smul' := fun a v => by rw [hc, hτ, h.bar_bar, RingHom.id_apply]
      left_inv := fun v => by
        change c.symm (τ.symm (τ (c v))) = v
        rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
      right_inv := fun v => by
        change τ (c (c.symm (τ.symm v))) = v
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] }
  have hconj : semiConjEnd h τ hτ g =
      (L : V →ₗ[E] V) ∘ₗ semiConjEnd h c hc g ∘ₗ (L.symm : V →ₗ[E] V) := by
    refine LinearMap.ext fun v => ?_
    change τ (g (τ.symm v)) = τ (c (c (g (c.symm (c.symm (τ.symm v))))))
    rw [coordConj_symm_apply, coordConj_symm_apply]
    change τ (g (τ.symm v)) = τ (c (c.symm (g (c (c.symm (τ.symm v))))))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hmat : LinearMap.toMatrix b b (semiConjEnd h c hc g) =
      (LinearMap.toMatrix b b g).map h.bar := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, semiConjEnd_apply,
      coordConj_symm_apply, coordConj_basis, repr_coordConj]
  rw [hconj, LinearMap.det_conj, ← LinearMap.det_toMatrix b, hmat, ← LinearMap.det_toMatrix b,
    RingHom.map_det]
  rfl

end Det

section NegOne

variable {σ : E →+* E} (B : V →ₛₗ[σ] V →ₗ[E] E)

@[expose] def negOneUnitary : sesqUnitaryGroup B :=
  ⟨-1, fun x y => by
    change B (-x) (-y) = B x y
    simp only [map_neg, LinearMap.neg_apply, neg_neg]⟩

theorem unitaryOp_negOneUnitary :
    ((negOneUnitary B : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = -1 := by
  change ((-1 : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = -1
  rw [Units.val_neg, Units.val_one]

end NegOne

section Unitary

variable (h : UnitaryFieldData p f E) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (τ : V ≃+ V)
  (hτ : ∀ (c : E) (v : V), τ (c • v) = h.bar c • τ v)
  (hτB : ∀ v w, B (τ v) (τ w) = h.bar (B v w))

include hτB in
theorem symm_form (v w : V) : B (τ.symm v) (τ.symm w) = h.bar (B v w) := by
  have h1 := hτB (τ.symm v) (τ.symm w)
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h1
  rw [h1, h.bar_bar]

include hτB in
theorem semiConjGL_mem {g : LinearMap.GeneralLinearGroup E V} (hg : g ∈ sesqUnitaryGroup B) :
    semiConjGL h τ hτ g ∈ sesqUnitaryGroup B := by
  intro x y
  change B (τ ((g : V →ₗ[E] V) (τ.symm x))) (τ ((g : V →ₗ[E] V) (τ.symm y))) = B x y
  rw [hτB, hg, ← hτB, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

include hτB in
theorem map_sesqUnitaryGroup_semiConjGL :
    (sesqUnitaryGroup B).map (semiConjGL h τ hτ).toMonoidHom = sesqUnitaryGroup B := by
  refine le_antisymm ?_ fun g hg =>
    ⟨(semiConjGL h τ hτ).symm g, ?_, MulEquiv.apply_symm_apply _ _⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact semiConjGL_mem h τ hτ hτB hg
  · exact semiConjGL_mem h τ.symm (symm_map_smul h τ hτ) (symm_form h τ hτB) hg

@[expose] def unitaryConj : MulAut (sesqUnitaryGroup B) :=
  CatalogueBOrthogonalLinearFixed.restrictAutomorphism _ (semiConjGL h τ hτ)
    (map_sesqUnitaryGroup_semiConjGL h τ hτ hτB)

theorem unitaryOp_unitaryConj (g : sesqUnitaryGroup B) :
    unitaryOp (unitaryConj h τ hτ hτB g) = semiConjEnd h τ hτ (unitaryOp g) :=
  rfl

theorem unitaryOp_unitaryConj_symm (g : sesqUnitaryGroup B) :
    unitaryOp ((unitaryConj h τ hτ hτB).symm g) =
      semiConjEnd h τ.symm (symm_map_smul h τ hτ) (unitaryOp g) := by
  change (((((unitaryConj h τ hτ hτB).symm g : sesqUnitaryGroup B) :
    LinearMap.GeneralLinearGroup E V)) : V →ₗ[E] V) = _
  rw [unitaryConj, CatalogueBOrthogonalLinearFixed.restrictAutomorphism_symm_apply]
  rfl

theorem unitaryConj_mem_scalars {g : sesqUnitaryGroup B} (hg : g ∈ sesqNormOneScalars h B) :
    unitaryConj h τ hτ hτB g ∈ sesqNormOneScalars h B := by
  obtain ⟨c, hc, hgc⟩ := hg
  refine ⟨h.bar c, ?_, ?_⟩
  · rw [UnitaryFieldData.norm, h.bar_bar, mul_comm]
    exact hc
  · change unitaryOp (unitaryConj h τ hτ hτB g) = h.bar c • 1
    rw [unitaryOp_unitaryConj, unitaryOp, hgc, semiConjEnd_smul_one]

theorem map_scalars_unitaryConj :
    (sesqNormOneScalars h B).map (unitaryConj h τ hτ hτB).toMonoidHom =
      sesqNormOneScalars h B := by
  refine le_antisymm ?_ fun z hz =>
    ⟨(unitaryConj h τ hτ hτB).symm z, ?_, MulEquiv.apply_symm_apply _ _⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact unitaryConj_mem_scalars h τ hτ hτB hz
  · obtain ⟨c, hc, hzc⟩ := hz
    refine ⟨h.bar c, ?_, ?_⟩
    · rw [UnitaryFieldData.norm, h.bar_bar, mul_comm]
      exact hc
    · change unitaryOp ((unitaryConj h τ hτ hτB).symm z) = h.bar c • 1
      rw [unitaryOp_unitaryConj_symm, unitaryOp, hzc, semiConjEnd_smul_one]

theorem unitaryConj_mem_special [FiniteDimensional E V] {g : sesqUnitaryGroup B}
    (hg : g ∈ unitarySpecial B) : unitaryConj h τ hτ hτB g ∈ unitarySpecial B := by
  rw [mem_unitarySpecial] at hg ⊢
  change LinearMap.det (unitaryOp (unitaryConj h τ hτ hτB g)) = 1
  rw [unitaryOp_unitaryConj, det_semiConjEnd, unitaryOp, hg, map_one]

theorem map_special_unitaryConj [FiniteDimensional E V] :
    (unitarySpecial B).map (unitaryConj h τ hτ hτB).toMonoidHom = unitarySpecial B := by
  refine le_antisymm ?_ fun g hg =>
    ⟨(unitaryConj h τ hτ hτB).symm g, ?_, MulEquiv.apply_symm_apply _ _⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact unitaryConj_mem_special h τ hτ hτB hg
  · rw [mem_unitarySpecial] at hg
    rw [SetLike.mem_coe, mem_unitarySpecial]
    change LinearMap.det (unitaryOp ((unitaryConj h τ hτ hτB).symm g)) = 1
    rw [unitaryOp_unitaryConj_symm, det_semiConjEnd, unitaryOp, hg, map_one]

abbrev projConj : MulAut (sesqProjUnitary h B) :=
  onQuotient (sesqNormOneScalars h B) (unitaryConj h τ hτ hτB) (map_scalars_unitaryConj h τ hτ hτB)

theorem projConj_mk (g : sesqUnitaryGroup B) :
    projConj h τ hτ hτB (QuotientGroup.mk g) = QuotientGroup.mk (unitaryConj h τ hτ hτB g) :=
  onQuotient_mk _ _ _ g

theorem map_projSpecial_projConj [FiniteDimensional E V] :
    (projSpecial h B).map (projConj h τ hτ hτB).toMonoidHom = projSpecial h B := by
  have hcomm : (projConj h τ hτ hτB).toMonoidHom.comp (QuotientGroup.mk' (sesqNormOneScalars h B)) =
      (QuotientGroup.mk' (sesqNormOneScalars h B)).comp (unitaryConj h τ hτ hτB).toMonoidHom :=
    MonoidHom.ext fun g => projConj_mk h τ hτ hτB g
  rw [projSpecial, Subgroup.map_map, hcomm, ← Subgroup.map_map, map_special_unitaryConj]

theorem unitaryConj_unitaryConj (μ : Eˣ) (hμ : ∀ v, τ (τ v) = (μ : E) • v)
    (g : sesqUnitaryGroup B) : unitaryConj h τ hτ hτB (unitaryConj h τ hτ hτB g) = g := by
  have hsymm : ∀ v, τ.symm (τ.symm v) = (μ : E)⁻¹ • v := fun v => by
    apply τ.injective
    apply τ.injective
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hμ, smul_smul,
      mul_inv_cancel₀ μ.ne_zero, one_smul]
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  change τ (τ (unitaryOp g (τ.symm (τ.symm v)))) = unitaryOp g v
  rw [hsymm, map_smul, hμ, smul_smul, mul_inv_cancel₀ μ.ne_zero, one_smul]

theorem projConj_mul_self (μ : Eˣ) (hμ : ∀ v, τ (τ v) = (μ : E) • v) :
    projConj h τ hτ hτB * projConj h τ hτ hτB = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAut.mul_apply, projConj_mk, projConj_mk, unitaryConj_unitaryConj h τ hτ hτB μ hμ]
  rfl

theorem mem_fixed_unitaryConj (g : sesqUnitaryGroup B) :
    g ∈ FixedCommutingProduct.fixedSubgroup (unitaryConj h τ hτ hτB) ↔
      ∀ v, unitaryOp g (τ v) = τ (unitaryOp g v) := by
  change unitaryConj h τ hτ hτB g = g ↔ _
  constructor
  · intro hg v
    have h1 := congrArg (fun x : sesqUnitaryGroup B => unitaryOp x (τ v)) hg
    change τ (unitaryOp g (τ.symm (τ v))) = unitaryOp g (τ v) at h1
    rw [AddEquiv.symm_apply_apply] at h1
    exact h1.symm
  · intro hg
    refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
    change τ (unitaryOp g (τ.symm v)) = unitaryOp g v
    rw [← hg, AddEquiv.apply_symm_apply]

theorem negOneUnitary_mem_fixed :
    negOneUnitary B ∈ FixedCommutingProduct.fixedSubgroup (unitaryConj h τ hτ hτB) := by
  have h1 : unitaryOp (negOneUnitary B) = -1 := unitaryOp_negOneUnitary B
  rw [mem_fixed_unitaryConj, h1]
  intro v
  rw [LinearMap.neg_apply, Module.End.one_apply, LinearMap.neg_apply, Module.End.one_apply,
    map_neg]

theorem fixed_mem_scalars_iff [FiniteDimensional E V] (hn : 1 ≤ finrank E V)
    (g : FixedCommutingProduct.fixedSubgroup (unitaryConj h τ hτ hτB)) :
    (g : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B ↔
      unitaryOp (g : sesqUnitaryGroup B) = 1 ∨ unitaryOp (g : sesqUnitaryGroup B) = -1 := by
  have hcomm := (mem_fixed_unitaryConj h τ hτ hτB _).mp g.2
  constructor
  · rintro ⟨c, hc, hgc⟩
    obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := E) (M := V)).mp (by omega)
    have hτv : τ v ≠ 0 := fun h0 => hv (τ.injective (h0.trans (map_zero τ).symm))
    have h1 := hcomm v
    have hgc' : unitaryOp (g : sesqUnitaryGroup B) = c • 1 := hgc
    rw [hgc', LinearMap.smul_apply, Module.End.one_apply, LinearMap.smul_apply,
      Module.End.one_apply, hτ] at h1
    have hcb : c = h.bar c := smul_left_injective E hτv h1
    have hcc : c * c = 1 := by
      rw [UnitaryFieldData.norm, ← hcb] at hc
      exact hc
    rcases mul_self_eq_one_iff.mp hcc with rfl | rfl
    · left
      rw [hgc', one_smul]
    · right
      rw [hgc', neg_one_smul]
  · rintro (h1 | h1)
    · exact ⟨1, by rw [UnitaryFieldData.norm, map_one, one_mul], by rw [one_smul]; exact h1⟩
    · refine ⟨-1, by rw [UnitaryFieldData.norm, map_neg, map_one, neg_one_mul, neg_neg], ?_⟩
      rw [neg_one_smul]
      exact h1

end Unitary

section Anti

variable (h : UnitaryFieldData p f E) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (τ₀ : V →ₛₗ[h.bar] V)
  (hτ₀ : Function.Bijective τ₀) (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w))

theorem sesqNormOneScalars_le_center (B : V →ₛₗ[h.bar] V →ₗ[E] E) :
    sesqNormOneScalars h B ≤ Subgroup.center (sesqUnitaryGroup B) := fun _ hz =>
  Subgroup.mem_center_iff.mpr fun x => (mem_sesqNormOneScalars_commute hz x).symm

abbrev antiEquiv : V ≃+ V :=
  AddEquiv.ofBijective τ₀.toAddMonoidHom hτ₀

abbrev antiConj : MulAut (sesqUnitaryGroup B) :=
  unitaryConj h (antiEquiv h τ₀ hτ₀) (fun c v => map_smulₛₗ τ₀ c v) hτ₀B

abbrev antiProjConj : MulAut (sesqProjUnitary h B) :=
  projConj h (antiEquiv h τ₀ hτ₀) (fun c v => map_smulₛₗ τ₀ c v) hτ₀B

abbrev antiFixedImage :
    Subgroup (FixedCommutingProduct.fixedSubgroup (antiProjConj h τ₀ hτ₀ hτ₀B)) :=
  fixedImage (sesqNormOneScalars h B) (antiConj h τ₀ hτ₀ hτ₀B)
    (map_scalars_unitaryConj h _ _ hτ₀B)

abbrev antiFixedProjection :
    FixedCommutingProduct.fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B) →*
      antiFixedImage h τ₀ hτ₀ hτ₀B :=
  fixedImageProjection (sesqNormOneScalars h B) (antiConj h τ₀ hτ₀ hτ₀B)
    (map_scalars_unitaryConj h _ _ hτ₀B)

end Anti

theorem one_ne_neg_one_end (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    (hn : 1 ≤ finrank E V) : (1 : Module.End E V) ≠ -1 := by
  intro h1
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := E) (M := V)).mp (by omega)
  have h2 := congrArg (fun φ : Module.End E V => φ v) h1
  simp only [Module.End.one_apply, LinearMap.neg_apply] at h2
  have h3 : (2 : E) • v = 0 := by rw [two_smul]; nth_rewrite 1 [h2]; exact neg_add_cancel v
  exact hv ((smul_eq_zero.mp h3).resolve_left (two_ne_zero_of_odd h hp))

theorem odd_unitary_semilinear_projective_fixed_structure (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) [FiniteDimensional E V] (hn : 1 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v) :
    (∀ (g : sesqUnitaryGroup B) (v : V),
      unitaryOp (antiConj h τ₀ hτ₀ hτ₀B g) (τ₀ v) = τ₀ (unitaryOp g v)) ∧
    (∀ g : sesqUnitaryGroup B, antiProjConj h τ₀ hτ₀ hτ₀B (QuotientGroup.mk g) =
      QuotientGroup.mk (antiConj h τ₀ hτ₀ hτ₀B g)) ∧
    antiProjConj h τ₀ hτ₀ hτ₀B * antiProjConj h τ₀ hτ₀ hτ₀B = 1 ∧
    (projSpecial h B).map (antiProjConj h τ₀ hτ₀ hτ₀B).toMonoidHom = projSpecial h B ∧
    (∀ g : sesqUnitaryGroup B,
      g ∈ FixedCommutingProduct.fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B) ↔
        ∀ v, unitaryOp g (τ₀ v) = τ₀ (unitaryOp g v)) ∧
    (antiFixedImage h τ₀ hτ₀ hτ₀B).Normal ∧
    (letI := fixedImage_normal (sesqNormOneScalars h B) (antiConj h τ₀ hτ₀ hτ₀B)
        (map_scalars_unitaryConj h _ _ hτ₀B) (sesqNormOneScalars_le_center h B);
      IsMulCommutative (FixedCommutingProduct.fixedSubgroup (antiProjConj h τ₀ hτ₀ hτ₀B) ⧸
        antiFixedImage h τ₀ hτ₀ hτ₀B)) ∧
    Function.Surjective (antiFixedProjection h τ₀ hτ₀ hτ₀B) ∧
    (∀ g, antiFixedProjection h τ₀ hτ₀ hτ₀B g = 1 ↔
      unitaryOp (g : sesqUnitaryGroup B) = 1 ∨ unitaryOp (g : sesqUnitaryGroup B) = -1) ∧
    (∃ g : FixedCommutingProduct.fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B),
      unitaryOp (g : sesqUnitaryGroup B) = -1) ∧
    (1 : Module.End E V) ≠ -1 ∧
    (antiFixedProjection h τ₀ hτ₀ hτ₀B).ker ≤
      Subgroup.center (FixedCommutingProduct.fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B)) ∧
    ((projSpecial h B).subgroupOf
      (FixedCommutingProduct.fixedSubgroup (antiProjConj h τ₀ hτ₀ hτ₀B))).Normal ∧
    ∃ e : unitarySpecial B ⧸ (sesqNormOneScalars h B).subgroupOf (unitarySpecial B) ≃*
        projSpecial h B,
      ∀ g : unitarySpecial B,
        (e (QuotientGroup.mk g) : sesqProjUnitary h B) =
          QuotientGroup.mk (g : sesqUnitaryGroup B) := by
  have hcentral := sesqNormOneScalars_le_center h B
  refine ⟨fun g v => ?_, projConj_mk h _ _ hτ₀B,
    projConj_mul_self h _ _ hτ₀B μ hμ, map_projSpecial_projConj h _ _ hτ₀B,
    mem_fixed_unitaryConj h _ _ hτ₀B, fixedImage_normal _ _ _ hcentral,
    fixed_quotient_abelian _ _ _ hcentral, fixedImageProjection_surjective _ _ _,
    fun g => ?_, ⟨⟨negOneUnitary B, negOneUnitary_mem_fixed h _ _ hτ₀B⟩,
      unitaryOp_negOneUnitary B⟩, one_ne_neg_one_end h hp hn,
    fixedImageProjection_kernel_central _ _ _ hcentral,
    (projSpecial_normal h B).subgroupOf _, specialQuotientEquiv h B,
    specialQuotientEquiv_mk h B⟩
  · change (antiEquiv h τ₀ hτ₀) (unitaryOp g ((antiEquiv h τ₀ hτ₀).symm (τ₀ v))) = _
    rw [show τ₀ v = antiEquiv h τ₀ hτ₀ v from rfl, AddEquiv.symm_apply_apply]
    rfl
  · rw [← MonoidHom.mem_ker, fixedImageProjection_kernel, Subgroup.mem_subgroupOf]
    exact fixed_mem_scalars_iff h _ _ hτ₀B hn g

end CFSG.ComponentClassification.CatalogueBUnitaryB
