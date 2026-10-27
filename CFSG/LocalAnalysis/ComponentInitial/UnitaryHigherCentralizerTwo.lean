module

public import CFSG.LocalAnalysis.ComponentInitial.LinearDoubleSL2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoEndpoint
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module Matrix

section LinearAut

variable {k : Type*} [Field k] {W V' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup V']
  [Module k V']

@[expose] noncomputable def glConj (Ψ : W ≃ₗ[k] V') :
    LinearMap.GeneralLinearGroup k V' →* LinearMap.GeneralLinearGroup k W where
  toFun x :=
    { val := Ψ.symm.toLinearMap ∘ₗ (x : V' →ₗ[k] V') ∘ₗ Ψ.toLinearMap
      inv := Ψ.symm.toLinearMap ∘ₗ ((x⁻¹ : LinearMap.GeneralLinearGroup k V') : V' →ₗ[k] V') ∘ₗ
        Ψ.toLinearMap
      val_inv := LinearMap.ext fun w => by
        change Ψ.symm ((x : V' →ₗ[k] V') (Ψ (Ψ.symm
          (((x⁻¹ : LinearMap.GeneralLinearGroup k V') : V' →ₗ[k] V') (Ψ w))))) = w
        rw [LinearEquiv.apply_symm_apply, ← Module.End.mul_apply, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, Module.End.one_apply, LinearEquiv.symm_apply_apply]
      inv_val := LinearMap.ext fun w => by
        change Ψ.symm (((x⁻¹ : LinearMap.GeneralLinearGroup k V') : V' →ₗ[k] V') (Ψ (Ψ.symm
          ((x : V' →ₗ[k] V') (Ψ w))))) = w
        rw [LinearEquiv.apply_symm_apply, ← Module.End.mul_apply, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, Module.End.one_apply, LinearEquiv.symm_apply_apply] }
  map_one' := Units.ext (LinearMap.ext fun w => Ψ.symm_apply_apply w)
  map_mul' x y := Units.ext (LinearMap.ext fun w => by
    change Ψ.symm ((x : V' →ₗ[k] V') ((y : V' →ₗ[k] V') (Ψ w))) =
      Ψ.symm ((x : V' →ₗ[k] V') (Ψ (Ψ.symm ((y : V' →ₗ[k] V') (Ψ w)))))
    rw [LinearEquiv.apply_symm_apply])

theorem glConj_apply (Ψ : W ≃ₗ[k] V') (x : LinearMap.GeneralLinearGroup k V') (w : W) :
    ((glConj Ψ x : LinearMap.GeneralLinearGroup k W) : W →ₗ[k] W) w =
      Ψ.symm ((x : V' →ₗ[k] V') (Ψ w)) :=
  rfl

theorem glConj_injective (Ψ : W ≃ₗ[k] V') : Function.Injective (glConj Ψ) := by
  intro x y hxy
  refine Units.ext (LinearMap.ext fun v => ?_)
  have h1 := congrArg (fun z : LinearMap.GeneralLinearGroup k W =>
    (z : W →ₗ[k] W) (Ψ.symm v)) hxy
  simp only [glConj_apply, LinearEquiv.apply_symm_apply] at h1
  exact Ψ.symm.injective h1

end LinearAut

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

@[expose] def glRestrictScalars (k : Subfield E) :
    LinearMap.GeneralLinearGroup E V →* LinearMap.GeneralLinearGroup k V :=
  Units.map
    { toFun := fun g => g.restrictScalars k
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem coe_glRestrictScalars (k : Subfield E) (g : LinearMap.GeneralLinearGroup E V) (v : V) :
    ((glRestrictScalars k g : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) v =
      (g : V →ₗ[E] V) v :=
  rfl

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBUnitaryTwo in
theorem exists_sl_conj (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    (hm : finrank E V = 2) {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm)
    (hnd : Hf.Nondegenerate) :
    ∃ Ψ : (E × E) ≃ₗ[h.fixedField] V, ∀ N : SpecialLinearGroup (Fin 2) h.fixedField,
      ∃ g ∈ sesqSpecialUnitaryGroup Hf,
        glConj Ψ (glRestrictScalars h.fixedField g) = doubleNaturalSL2 N := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨-, B₀, t, eSL, -, -, -, -, hback⟩ :=
    odd_unitary_two_special_linear_isomorphism p f hp h.one_le h.card_eq_sq Hf hH hnd hm
  have hle : h.fixedField ≤
      CatalogueBLinearTwoDescent.fixedSubfield E (unitaryFieldConjugation p f h.card_eq_sq) := by
    intro x hx
    rw [CatalogueBLinearTwoDescent.mem_fixedSubfield]
    exact h.mem_fixedField.mp hx
  obtain ⟨Dl, hDl⟩ : ∃ Dl : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E),
      ∀ v, Dl v = (diagonalGL t).val *ᵥ v :=
    ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv E _
      (Matrix.GeneralLinearGroup.toLin (diagonalGL t)), fun _ => rfl⟩
  obtain ⟨ΨE, hΨE⟩ : ∃ ΨE : (E × E) ≃ₗ[E] V,
      ∀ a b : E, ΨE (a, b) = B₀ ((diagonalGL t).val *ᵥ ![a, b]) :=
    ⟨(LinearEquiv.finTwoArrow E E).symm.trans (Dl.trans B₀), fun a b => by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hDl]
      rfl⟩
  refine ⟨ΨE.restrictScalars h.fixedField, fun N => ?_⟩
  obtain ⟨N', hN'⟩ : ∃ N' : SpecialLinearGroup (Fin 2)
      (CatalogueBLinearTwoDescent.fixedSubfield E (unitaryFieldConjugation p f h.card_eq_sq)),
      ∀ i j, ((N' : Matrix (Fin 2) (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E
        (unitaryFieldConjugation p f h.card_eq_sq))) i j : E) =
          ((N : Matrix (Fin 2) (Fin 2) h.fixedField) i j : E) :=
    ⟨SpecialLinearGroup.map (Subfield.inclusion hle) N, fun _ _ => rfl⟩
  set g' := eSL.symm N' with hg'
  have hgB : ∀ u, g'.val.val (B₀ u) = B₀ (((diagonalGL t).val *
      (fixedSLMap (unitaryFieldConjugation p f h.card_eq_sq) N').val *
        (diagonalGL t)⁻¹.val) *ᵥ u) := by
    intro u
    rw [← hback N', LinearMap.toMatrix'_mulVec]
    simp [hg']
  refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm g'.val.val,
    mem_sesqSpecialUnitaryGroup.mpr ⟨mem_sesqUnitaryGroup.mpr fun x y => g'.val.2 x y,
      (CatalogueBUnitaryIsometry.mem_specialIsometry_iff _ g'.val).mp g'.2⟩, ?_⟩
  refine Units.ext (LinearMap.ext fun w => ?_)
  obtain ⟨x, y⟩ := w
  rw [glConj_apply, coe_glRestrictScalars, doubleNaturalSL2_apply]
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  change g'.val.val (ΨE (x, y)) = ΨE (_, _)
  rw [hΨE, hΨE, hgB, mulVec_mulVec, Matrix.mul_assoc _ (diagonalGL t)⁻¹.val, Units.inv_mul,
    Matrix.mul_one, ← mulVec_mulVec]
  congr 2
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, fixedSLMap_entry, hN',
    Subfield.smul_def]

theorem centralizer_solvable_two (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    (hm : finrank E V = 2) {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm)
    (hnd : Hf.Nondegenerate) (B : LinearMap.BilinForm h.fixedField V) (hB : B.Nondegenerate)
    (hBalt : B.IsAlt)
    (hinv : ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∀ u v,
      B ((g : V →ₗ[E] V) u) ((g : V →ₗ[E] V) v) = B u v) :
    Group.IsSolvable (Subgroup.centralizer
      ((((sesqSpecialUnitaryGroup Hf).map (glRestrictScalars h.fixedField)).subgroupOf
        (bilinIsometryGroup B)) : Set (bilinIsometryGroup B))) := by
  obtain ⟨Ψ, hΨ⟩ := exists_sl_conj h hp hm hH hnd
  obtain ⟨B', hB'apply⟩ : ∃ B' : LinearMap.BilinForm h.fixedField (E × E),
      ∀ u w, B' u w = B (Ψ u) (Ψ w) := ⟨B.compl₁₂ Ψ.toLinearMap Ψ.toLinearMap, fun _ _ => rfl⟩
  have hB'nd : B'.Nondegenerate := by
    refine ⟨fun u hu => Ψ.injective ?_, fun w hw => Ψ.injective ?_⟩
    · rw [map_zero]
      refine hB.1 _ fun v => ?_
      have h1 := hu (Ψ.symm v)
      rwa [hB'apply, LinearEquiv.apply_symm_apply] at h1
    · rw [map_zero]
      refine hB.2 _ fun v => ?_
      have h1 := hw (Ψ.symm v)
      rwa [hB'apply, LinearEquiv.apply_symm_apply] at h1
  have hB'alt : B'.IsAlt := fun u => by rw [hB'apply]; exact hBalt (Ψ u)
  have hB'inv : ∀ (N : SpecialLinearGroup (Fin 2) h.fixedField) (u w : E × E),
      B' (((doubleNaturalSL2 N : LinearMap.GeneralLinearGroup h.fixedField (E × E)) :
        E × E →ₗ[h.fixedField] E × E) u)
        (((doubleNaturalSL2 N : LinearMap.GeneralLinearGroup h.fixedField (E × E)) :
          E × E →ₗ[h.fixedField] E × E) w) = B' u w := by
    intro N u w
    obtain ⟨g, hg, hgN⟩ := hΨ N
    rw [← hgN, hB'apply, hB'apply, glConj_apply, glConj_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, coe_glRestrictScalars, coe_glRestrictScalars]
    exact hinv g hg _ _
  have hk : ringChar h.fixedField ≠ 2 := by
    intro h2
    have h3 : ((2 : ℕ) : h.fixedField) = 0 := by
      rw [← h2]
      exact ringChar.Nat.cast_ringChar
    have h4 : ((2 : ℕ) : E) = 0 := by
      rw [← map_natCast h.fixedField.subtype 2, h3, map_zero]
    have : CharP E p := h.charP
    have h5 := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff E p 2).mp h4)
    have := h.prime.two_le
    omega
  have hW : finrank h.fixedField E = 2 := by
    have : Finite E := h.finite
    have h1 := Module.natCard_eq_pow_finrank (K := h.fixedField) (V := E)
    rw [h.card_eq_sq, h.card_fixedField] at h1
    exact (Nat.pow_right_injective (by have := h.one_lt_pow; omega) h1).symm
  have hsolv := double_natural_SL2_symplectic_centralizer_solvable hk hW B' hB'nd hB'alt hB'inv
  have hmemB' : ∀ x ∈ bilinIsometryGroup B, glConj Ψ x ∈ bilinIsometryGroup B' := by
    intro x hx
    rw [mem_bilinIsometryGroup] at hx ⊢
    intro u w
    rw [hB'apply, hB'apply, glConj_apply, glConj_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, hx]
  have hcent : ∀ x : Subgroup.centralizer
      ((((sesqSpecialUnitaryGroup Hf).map (glRestrictScalars h.fixedField)).subgroupOf
        (bilinIsometryGroup B)) : Set (bilinIsometryGroup B)),
      (⟨glConj Ψ x.1.1, hmemB' _ x.1.2⟩ : bilinIsometryGroup B') ∈ Subgroup.centralizer
        ((((doubleNaturalSL2 (k := h.fixedField) (W := E)).range).subgroupOf
          (bilinIsometryGroup B')) : Set (bilinIsometryGroup B')) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    rintro ⟨z, hzB'⟩ hz
    obtain ⟨N, hN⟩ := Subgroup.mem_subgroupOf.mp hz
    have hN' : doubleNaturalSL2 N = z := hN
    obtain ⟨g, hg, hgN⟩ := hΨ N
    have hgB : glRestrictScalars h.fixedField g ∈ bilinIsometryGroup B :=
      mem_bilinIsometryGroup.mpr fun u w => hinv g hg u w
    have hxc := (Subgroup.mem_centralizer_iff.mp x.2) ⟨_, hgB⟩
      (Subgroup.mem_subgroupOf.mpr ⟨g, hg, rfl⟩)
    apply Subtype.ext
    change z * glConj Ψ x.1.1 = glConj Ψ x.1.1 * z
    rw [← hN', ← hgN, ← map_mul, ← map_mul]
    exact congrArg (glConj Ψ) (congrArg Subtype.val hxc)
  let φ : Subgroup.centralizer
      ((((sesqSpecialUnitaryGroup Hf).map (glRestrictScalars h.fixedField)).subgroupOf
        (bilinIsometryGroup B)) : Set (bilinIsometryGroup B)) →* Subgroup.centralizer
          ((((doubleNaturalSL2 (k := h.fixedField) (W := E)).range).subgroupOf
            (bilinIsometryGroup B')) : Set (bilinIsometryGroup B')) :=
    { toFun := fun x => ⟨⟨glConj Ψ x.1.1, hmemB' _ x.1.2⟩, hcent x⟩
      map_one' := Subtype.ext (Subtype.ext (map_one (glConj Ψ)))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul (glConj Ψ) x.1.1 y.1.1)) }
  refine Group.isSolvable_of_isSolvable_injective (f := φ) fun x y hxy => ?_
  exact Subtype.ext (Subtype.ext (glConj_injective Ψ
    (congrArg Subtype.val (congrArg Subtype.val hxy))))

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
