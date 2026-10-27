module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionEigenspaces

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def operatorCentralizer (T : Module.End K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {B | ∀ x, B (T x) = T (B x)}
  one_mem' _ := rfl
  mul_mem' {B C} hB hC x := by
    change B (C (T x)) = T (B (C x))
    rw [hC, hB]
  inv_mem' {B} hB x := by
    apply B.injective
    change B (B.symm (T x)) = B (T (B.symm x))
    simpa only [LinearEquiv.apply_symm_apply] using (hB (B.symm x)).symm

theorem operatorCentralizer_preserves_eigenspace (T : Module.End K V) (b : K)
    (B : operatorCentralizer T) {x : V} (hx : x ∈ T.eigenspace b) :
    B.val x ∈ T.eigenspace b := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [← B.property, hx, map_smul]

@[expose] def operatorCentralizerRestriction (T : Module.End K V) (b : K)
    (B : operatorCentralizer T) : T.eigenspace b ≃ₗ[K] T.eigenspace b where
  toFun x := ⟨B.val x.val, operatorCentralizer_preserves_eigenspace T b B x.property⟩
  invFun x := ⟨B.val.symm x.val,
    operatorCentralizer_preserves_eigenspace T b B⁻¹ x.property⟩
  left_inv x := Subtype.ext (B.val.symm_apply_apply x.val)
  right_inv x := Subtype.ext (B.val.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add B.val x.val y.val)
  map_smul' c x := Subtype.ext (map_smul B.val c x.val)

theorem operatorCentralizerRestriction_apply (T : Module.End K V) (b : K)
    (B : operatorCentralizer T) (x : T.eigenspace b) :
    (operatorCentralizerRestriction T b B x).val = B.val x.val := rfl

@[expose] def splitCentralizerRestriction (T : Module.End K V) (b : K) :
    operatorCentralizer T →*
      ((T.eigenspace b ≃ₗ[K] T.eigenspace b) ×
        (T.eigenspace (-b) ≃ₗ[K] T.eigenspace (-b))) where
  toFun B := (operatorCentralizerRestriction T b B, operatorCentralizerRestriction T (-b) B)
  map_one' := by ext x <;> rfl
  map_mul' B C := by ext x <;> rfl

@[expose] def splitCentralizerExtension (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (B : (T.eigenspace b ≃ₗ[K] T.eigenspace b) ×
      (T.eigenspace (-b) ≃ₗ[K] T.eigenspace (-b))) : operatorCentralizer T := by
  let e := squareScalar_eigenspaceEquiv T b hb htwo hsquare
  refine ⟨(e.symm.trans (B.1.prodCongr B.2)).trans e, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  have he (z : T.eigenspace b × T.eigenspace (-b)) :
      T (e z) = e (b • z.1, (-b) • z.2) := by
    change T (z.1.val + z.2.val) = b • z.1.val + (-b) • z.2.val
    rw [map_add, Module.End.mem_eigenspace_iff.mp z.1.property,
      Module.End.mem_eigenspace_iff.mp z.2.property]
  simp only [LinearEquiv.trans_apply, he, LinearEquiv.symm_apply_apply,
    LinearEquiv.prodCongr_apply, map_smul]

theorem splitCentralizerExtension_apply (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (B : (T.eigenspace b ≃ₗ[K] T.eigenspace b) ×
      (T.eigenspace (-b) ≃ₗ[K] T.eigenspace (-b)))
    (x : T.eigenspace b × T.eigenspace (-b)) :
    (splitCentralizerExtension T b hb htwo hsquare B).val
        (squareScalar_eigenspaceEquiv T b hb htwo hsquare x) =
      (B.1 x.1).val + (B.2 x.2).val := by
  simp [splitCentralizerExtension, squareScalar_eigenspaceEquiv]

theorem splitCentralizerRestriction_extension (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (B : (T.eigenspace b ≃ₗ[K] T.eigenspace b) ×
      (T.eigenspace (-b) ≃ₗ[K] T.eigenspace (-b))) :
    splitCentralizerRestriction T b (splitCentralizerExtension T b hb htwo hsquare B) = B := by
  apply Prod.ext
  · ext x
    change (splitCentralizerExtension T b hb htwo hsquare B).val x.val = (B.1 x).val
    simpa [squareScalar_eigenspaceEquiv] using
      splitCentralizerExtension_apply T b hb htwo hsquare B (x, 0)
  · ext x
    change (splitCentralizerExtension T b hb htwo hsquare B).val x.val = (B.2 x).val
    simpa [squareScalar_eigenspaceEquiv] using
      splitCentralizerExtension_apply T b hb htwo hsquare B (0, x)

theorem splitCentralizerExtension_restriction (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V)) (B : operatorCentralizer T) :
    splitCentralizerExtension T b hb htwo hsquare (splitCentralizerRestriction T b B) = B := by
  apply Subtype.ext
  ext x
  obtain ⟨y, rfl⟩ := (squareScalar_eigenspaceEquiv T b hb htwo hsquare).surjective x
  rw [splitCentralizerExtension_apply]
  change B.val y.1.val + B.val y.2.val = B.val (y.1.val + y.2.val)
  exact (map_add B.val _ _).symm

@[expose] def splitCentralizerEquiv (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V)) :
    operatorCentralizer T ≃*
      ((T.eigenspace b ≃ₗ[K] T.eigenspace b) ×
        (T.eigenspace (-b) ≃ₗ[K] T.eigenspace (-b))) where
  toFun := splitCentralizerRestriction T b
  invFun := splitCentralizerExtension T b hb htwo hsquare
  left_inv := splitCentralizerExtension_restriction T b hb htwo hsquare
  right_inv := splitCentralizerRestriction_extension T b hb htwo hsquare
  map_mul' := (splitCentralizerRestriction T b).map_mul

@[expose] def operatorCentralizerScalar (T : Module.End K V) : Kˣ →* operatorCentralizer T where
  toFun c := ⟨LinearEquiv.smulOfUnit c, fun x => (map_smul T c.val x).symm⟩
  map_one' := by ext x; simp [LinearEquiv.smulOfUnit]
  map_mul' c d := by ext x; simp [LinearEquiv.smulOfUnit, smul_smul]

theorem splitCentralizerEquiv_scalar (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V)) (c : Kˣ) :
    splitCentralizerEquiv T b hb htwo hsquare (operatorCentralizerScalar T c) =
      (LinearEquiv.smulOfUnit c, LinearEquiv.smulOfUnit c) := by
  ext x <;> rfl

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
