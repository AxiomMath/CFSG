module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap

public noncomputable section

namespace Derivation

open TauCeti

universe u v w
variable {R : Type u} [CommRing R]
section Bialgebra

variable {H : Type v} [CommRing H] [Bialgebra R H]
variable {A : Type w} [CommRing A] [Bialgebra R A]

private def compCounitAux (f : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A R)) :
    Derivation R H (Bialgebra.CounitAlgebra R H R) := by
  let eA := Bialgebra.CounitAlgebra.algEquivSelf R A R
  let eH := Bialgebra.CounitAlgebra.algEquivSelf R H R
  let θ := eA.toLinearEquiv.trans eH.symm.toLinearEquiv
  refine Derivation.mk' (θ.toLinearMap.comp
    ((d : A →ₗ[R] Bialgebra.CounitAlgebra R A R).comp f.toLinearMap)) ?_
  intro a b
  have ha := DFunLike.congr_fun hf a
  have hb := DFunLike.congr_fun hf b
  simp only [AlgHom.comp_apply, _root_.Bialgebra.counitAlgHom_apply] at ha hb
  apply eH.injective
  change eH (eH.symm (eA (d (f (a * b))))) =
    eH (a • eH.symm (eA (d (f b))) + b • eH.symm (eA (d (f a))))
  rw [AlgEquiv.apply_symm_apply, map_add]
  dsimp only [eA, eH]
  simp only [Bialgebra.CounitAlgebra.algEquivSelf_smul,
    AlgEquiv.apply_symm_apply]
  rw [map_mul, Bialgebra.CounitAlgebra.algEquivSelf_apply_mul]
  simp only [ha, hb]

private theorem compCounitAux_apply (f : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A R)) (a : H) :
    compCounitAux f hf d a =
      (Bialgebra.CounitAlgebra.algEquivSelf R H R).symm
        (Bialgebra.CounitAlgebra.algEquivSelf R A R (d (f a))) := by
  rfl

def compCounit (f : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H) :
    Derivation R A (Bialgebra.CounitAlgebra R A R) →ₗ[R]
      Derivation R H (Bialgebra.CounitAlgebra R H R) where
  toFun := compCounitAux f hf
  map_add' d e := by
    ext a
    simp only [compCounitAux_apply, Derivation.add_apply, map_add]
  map_smul' r d := by
    ext a
    apply (Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
    rw [compCounitAux_apply, AlgEquiv.apply_symm_apply,
      algEquivSelf_derivation_smul_apply, algEquivSelf_derivation_smul_apply,
      compCounitAux_apply, AlgEquiv.apply_symm_apply]
    simp only [RingHom.id_apply]

@[simp] theorem compCounit_apply (f : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A R)) (a : H) :
    compCounit f hf d a =
      (Bialgebra.CounitAlgebra.algEquivSelf R H R).symm
        (Bialgebra.CounitAlgebra.algEquivSelf R A R (d (f a))) :=
  compCounitAux_apply f hf d a

theorem compCounit_toAlgHom (f : H →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A R)) :
    compCounit f.toAlgHom (_root_.BialgHom.counitAlgHom_comp f) d =
      derivationComp (B := R) f d := by
  ext a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
  rw [compCounit_apply, AlgEquiv.apply_symm_apply]
  exact (algEquivSelf_derivationComp_apply (B := R) f d a).symm

end Bialgebra

section Hopf

open _root_.Coalgebra TensorProduct WithConv

variable {H : Type v} [CommRing H] [HopfAlgebra R H]
variable {A : Type w} [CommRing A] [Bialgebra R A]

theorem counit_comp_convMul (f g : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (hg : (_root_.Bialgebra.counitAlgHom R A).comp g =
      _root_.Bialgebra.counitAlgHom R H) :
    (_root_.Bialgebra.counitAlgHom R A).comp (toConv f * toConv g).ofConv =
      _root_.Bialgebra.counitAlgHom R H := by
  apply toConv_injective
  rw [AlgHom.comp_convMul_distrib, hf, hg]
  have hε : toConv (_root_.Bialgebra.counitAlgHom R H) =
      (1 : WithConv (H →ₐ[R] R)) := by
    apply WithConv.ext
    rw [AlgHom.convOne_def]
    ext a
    simp
  rw [hε, one_mul]

private theorem scalar_derivation_comp_convMul (f g : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (hg : (_root_.Bialgebra.counitAlgHom R A).comp g =
      _root_.Bialgebra.counitAlgHom R H)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A R)) :
    ((Bialgebra.CounitAlgebra.algEquivSelf R A R).toLinearMap.comp
      (d : A →ₗ[R] Bialgebra.CounitAlgebra R A R)).comp
        (toConv f * toConv g).ofConv.toLinearMap =
    ((Bialgebra.CounitAlgebra.algEquivSelf R A R).toLinearMap.comp
      (d : A →ₗ[R] Bialgebra.CounitAlgebra R A R)).comp f.toLinearMap +
    ((Bialgebra.CounitAlgebra.algEquivSelf R A R).toLinearMap.comp
      (d : A →ₗ[R] Bialgebra.CounitAlgebra R A R)).comp g.toLinearMap := by
  let D := (Bialgebra.CounitAlgebra.algEquivSelf R A R).toLinearMap.comp
    (d : A →ₗ[R] Bialgebra.CounitAlgebra R A R)
  change D.comp _ = D.comp _ + D.comp _
  have hD (a b : A) : D (a * b) = counit a * D b + counit b * D a := by
    change Bialgebra.CounitAlgebra.algEquivSelf R A R (d (a * b)) = _
    rw [Bialgebra.CounitAlgebra.algEquivSelf_apply_mul]
    rfl
  have hfε (a : H) : counit (R := R) (f a) = counit a := by
    simpa only [AlgHom.comp_apply, _root_.Bialgebra.counitAlgHom_apply] using
      DFunLike.congr_fun hf a
  have hgε (a : H) : counit (R := R) (g a) = counit a := by
    simpa only [AlgHom.comp_apply, _root_.Bialgebra.counitAlgHom_apply] using
      DFunLike.congr_fun hg a
  have h1 : (toConv f * toConv g).ofConv.toLinearMap =
      LinearMap.mul' R A ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap ∘ₗ comul := by
    have h := AlgHom.toLinearMap_convMul (toConv f) (toConv g)
    rw [LinearMap.convMul_def] at h
    exact congrArg ofConv h
  have h2 : D ∘ₗ LinearMap.mul' R A ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap =
      LinearMap.mul' R R ∘ₗ TensorProduct.map (D ∘ₗ f.toLinearMap) counit +
        LinearMap.mul' R R ∘ₗ TensorProduct.map counit (D ∘ₗ g.toLinearMap) := by
    refine TensorProduct.ext' fun a b => ?_
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
      AlgHom.toLinearMap_apply, LinearMap.add_apply]
    rw [hD, hfε, hgε]
    rw [mul_comm (counit b) (D (f a))]
    exact add_comm _ _
  have h3 : ∀ u v : H →ₗ[R] R,
      LinearMap.mul' R R ∘ₗ TensorProduct.map u v ∘ₗ comul =
        (toConv u * toConv v).ofConv := fun u v => rfl
  have hone : (counit : H →ₗ[R] R) = (1 : WithConv (H →ₗ[R] R)).ofConv := by
    rw [LinearMap.convOne_def]
    ext a
    simp
  rw [h1]
  change (D ∘ₗ LinearMap.mul' R A ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap) ∘ₗ
    comul = _
  rw [h2, LinearMap.add_comp]
  simp only [LinearMap.comp_assoc]
  rw [h3, h3, hone]
  simp

theorem compCounit_convMul (f g : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (hg : (_root_.Bialgebra.counitAlgHom R A).comp g =
      _root_.Bialgebra.counitAlgHom R H) :
    compCounit (toConv f * toConv g).ofConv (counit_comp_convMul f g hf hg) =
      compCounit f hf + compCounit g hg := by
  ext d a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
  simp only [compCounit_apply, LinearMap.add_apply, Derivation.add_apply, map_add,
    AlgEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (scalar_derivation_comp_convMul f g hf hg d) a

theorem counit_comp_convOne :
    (_root_.Bialgebra.counitAlgHom R A).comp
        (1 : WithConv (H →ₐ[R] A)).ofConv =
      _root_.Bialgebra.counitAlgHom R H := by
  ext a
  simp [AlgHom.convOne_def, Algebra.ofId_apply]

theorem compCounit_convOne :
    compCounit (1 : WithConv (H →ₐ[R] A)).ofConv counit_comp_convOne = 0 := by
  ext d a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
  simp only [compCounit_apply, AlgEquiv.apply_symm_apply, LinearMap.zero_apply,
    Derivation.zero_apply, map_zero]
  rw [AlgHom.convOne_def, ofConv_toConv, AlgHom.comp_apply, Algebra.ofId_apply,
    Algebra.algebraMap_eq_smul_one, map_smul, d.map_one_eq_zero, smul_zero, map_zero]

theorem counit_comp_convInv (f : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H) :
    (_root_.Bialgebra.counitAlgHom R A).comp (toConv f)⁻¹.ofConv =
      _root_.Bialgebra.counitAlgHom R H := by
  rw [WithConv.convInv_def, ofConv_toConv]
  ext a
  rw [AlgHom.comp_apply, AlgHom.antipodeComp_apply]
  change ((_root_.Bialgebra.counitAlgHom R A).comp f) _ = _
  rw [hf]
  change ((_root_.Bialgebra.counitAlgHom R H).comp
    (_root_.HopfAlgebra.antipodeAlgHom R H)) a =
      _root_.Bialgebra.counitAlgHom R H a
  rw [AlgHom.counitAlgHom_comp_antipodeAlgHom]

theorem compCounit_convInv (f : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H) :
    compCounit (toConv f)⁻¹.ofConv (counit_comp_convInv f hf) =
      -compCounit f hf := by
  have h := compCounit_convMul f (toConv f)⁻¹.ofConv hf
    (counit_comp_convInv f hf)
  simp only [toConv_ofConv, mul_inv_cancel, compCounit_convOne] at h
  ext d a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
  have he := congrArg
    (fun L => Bialgebra.CounitAlgebra.algEquivSelf R H R (L d a)) h
  simp only [LinearMap.zero_apply, Derivation.zero_apply, map_zero,
    LinearMap.add_apply, Derivation.add_apply, map_add] at he
  have hn := eq_neg_of_add_eq_zero_right he.symm
  simpa only [LinearMap.neg_apply, Derivation.neg_apply, map_neg] using hn

theorem counit_comp_convMul_convInv (f g h : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (hg : (_root_.Bialgebra.counitAlgHom R A).comp g =
      _root_.Bialgebra.counitAlgHom R H)
    (hh : (_root_.Bialgebra.counitAlgHom R A).comp h =
      _root_.Bialgebra.counitAlgHom R H) :
    (_root_.Bialgebra.counitAlgHom R A).comp
        (toConv f * toConv g * (toConv h)⁻¹).ofConv =
      _root_.Bialgebra.counitAlgHom R H := by
  simpa only [toConv_ofConv] using
    counit_comp_convMul (toConv f * toConv g).ofConv (toConv h)⁻¹.ofConv
      (counit_comp_convMul f g hf hg) (counit_comp_convInv h hh)

theorem compCounit_convMul_convInv (f g h : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (hg : (_root_.Bialgebra.counitAlgHom R A).comp g =
      _root_.Bialgebra.counitAlgHom R H)
    (hh : (_root_.Bialgebra.counitAlgHom R A).comp h =
      _root_.Bialgebra.counitAlgHom R H) :
    compCounit (toConv f * toConv g * (toConv h)⁻¹).ofConv
        (counit_comp_convMul_convInv f g h hf hg hh) =
      compCounit f hf + compCounit g hg + -compCounit h hh := by
  calc
    _ = compCounit (toConv f * toConv g).ofConv (counit_comp_convMul f g hf hg) +
        compCounit (toConv h)⁻¹.ofConv (counit_comp_convInv h hh) := by
      simpa only [toConv_ofConv] using
        compCounit_convMul (toConv f * toConv g).ofConv (toConv h)⁻¹.ofConv
          (counit_comp_convMul f g hf hg) (counit_comp_convInv h hh)
    _ = _ := by
      rw [compCounit_convMul f g hf hg, compCounit_convInv h hh]

end Hopf

end Derivation
