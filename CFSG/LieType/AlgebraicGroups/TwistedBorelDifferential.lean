module

public import CFSG.LieType.AlgebraicGroups.PointedDerivation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Product

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TauCeti WithConv
open scoped TensorProduct

universe u v
variable {k : Type u} [CommRing k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H]

@[expose] def normalizedTwistedBorelCoordinateMap (I : HopfIdeal k H) (θ : H →ₐc[k] H) :
    H →ₐ[k] H ⊗[k] (H ⧸ I.toIdeal) :=
  (toConv (TauCeti.Bialgebra.TensorProduct.includeLeft
      (R := k) (H₁ := H) (H₂ := H ⧸ I.toIdeal)).toAlgHom *
    toConv ((TauCeti.Bialgebra.TensorProduct.includeRight
      (R := k) (H₁ := H) (H₂ := H ⧸ I.toIdeal)).comp
        (_root_.Bialgebra.Quotient.mkBialgHom I.toIdeal)).toAlgHom *
    (toConv ((TauCeti.Bialgebra.TensorProduct.includeLeft
      (R := k) (H₁ := H) (H₂ := H ⧸ I.toIdeal)).comp θ).toAlgHom)⁻¹).ofConv

theorem counit_comp_normalizedTwistedBorelCoordinateMap
    (I : HopfIdeal k H) (θ : H →ₐc[k] H) :
    (_root_.Bialgebra.counitAlgHom k (H ⊗[k] (H ⧸ I.toIdeal))).comp
        (normalizedTwistedBorelCoordinateMap I θ) =
      _root_.Bialgebra.counitAlgHom k H := by
  apply Derivation.counit_comp_convMul_convInv
  all_goals exact _root_.BialgHom.counitAlgHom_comp _

@[expose] def normalizedTwistedBorelDifferential (I : HopfIdeal k H) (θ : H →ₐc[k] H) :
    (Derivation k H (Bialgebra.CounitAlgebra k H k) ×
      Derivation k (H ⧸ I.toIdeal) (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) →ₗ[k]
        Derivation k H (Bialgebra.CounitAlgebra k H k) :=
  (Derivation.compCounit (normalizedTwistedBorelCoordinateMap I θ)
    (counit_comp_normalizedTwistedBorelCoordinateMap I θ)).comp
      (Derivation.tensorProductLieEquiv (R := k) (H₁ := H)
        (H₂ := H ⧸ I.toIdeal) (B := k)).toLinearEquiv.symm.toLinearMap

theorem normalizedTwistedBorelDifferential_eq
    (I : HopfIdeal k H) (θ : H →ₐc[k] H) :
    normalizedTwistedBorelDifferential I θ =
      (LinearMap.id - (derivationCompLieHom (B := k) θ).toLinearMap).coprod
        (I.quotientLieHom (B := k)).toLinearMap := by
  let L := TauCeti.Bialgebra.TensorProduct.includeLeft
    (R := k) (H₁ := H) (H₂ := H ⧸ I.toIdeal)
  let R := TauCeti.Bialgebra.TensorProduct.includeRight
    (R := k) (H₁ := H) (H₂ := H ⧸ I.toIdeal)
  let π := _root_.Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal
  let E := Derivation.tensorProductLieEquiv (R := k) (H₁ := H)
    (H₂ := H ⧸ I.toIdeal) (B := k)
  apply LinearMap.ext
  intro p
  apply Derivation.ext
  intro a
  let d := E.toLinearEquiv.symm p
  have hE : (derivationComp (B := k) L d, derivationComp (B := k) R d) = p := by
    rw [← Derivation.tensorProductLieEquiv_apply]
    exact E.toLinearEquiv.apply_symm_apply p
  have hL : derivationComp (B := k) L d = p.1 := congrArg Prod.fst hE
  have hR : derivationComp (B := k) R d = p.2 := congrArg Prod.snd hE
  have hQ : derivationComp (B := k) (R.comp π) d = I.quotientLieHom p.2 := by
    rw [derivationComp_comp, LinearMap.comp_apply, hR]
    exact (I.quotientLieHom_apply p.2).symm
  have hθ : derivationComp (B := k) (L.comp θ) d = derivationComp (B := k) θ p.1 := by
    rw [derivationComp_comp, LinearMap.comp_apply, hL]
  have hdiff := DFunLike.congr_fun
    (Derivation.compCounit_convMul_convInv L.toAlgHom (R.comp π).toAlgHom
      (L.comp θ).toAlgHom (_root_.BialgHom.counitAlgHom_comp L)
      (_root_.BialgHom.counitAlgHom_comp (R.comp π))
      (_root_.BialgHom.counitAlgHom_comp (L.comp θ))) d
  simp only [LinearMap.add_apply, LinearMap.neg_apply] at hdiff
  rw [Derivation.compCounit_toAlgHom L d,
    Derivation.compCounit_toAlgHom (R.comp π) d,
    Derivation.compCounit_toAlgHom (L.comp θ) d, hL, hQ, hθ] at hdiff
  apply (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
  simp only [LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LieHom.coe_toLinearMap, derivationCompLieHom_apply]
  change Bialgebra.CounitAlgebra.algEquivSelf k H k
      (Derivation.compCounit (normalizedTwistedBorelCoordinateMap I θ)
        (counit_comp_normalizedTwistedBorelCoordinateMap I θ) d a) =
    Bialgebra.CounitAlgebra.algEquivSelf k H k
      ((p.1 - derivationComp θ p.1 + I.quotientLieHom p.2) a)
  rw [show Derivation.compCounit (normalizedTwistedBorelCoordinateMap I θ)
        (counit_comp_normalizedTwistedBorelCoordinateMap I θ) d =
      p.1 + I.quotientLieHom p.2 + -derivationComp θ p.1 from hdiff]
  simp only [Derivation.add_apply, Derivation.neg_apply, Derivation.sub_apply,
    map_add, map_neg, map_sub]
  abel

theorem range_quotientLieHom_eq_lieSubalgebra (I : HopfIdeal k H) :
    LinearMap.range (I.quotientLieHom (B := k)).toLinearMap =
      (I.lieSubalgebra (B := k)).toSubmodule := by
  apply le_antisymm
  · rintro d ⟨q, rfl⟩
    have h := (I.quotientLieEquiv (B := k) q).property
    rw [I.quotientLieEquiv_apply_coe q] at h
    simpa only [LieHom.coe_toLinearMap] using
      (LieSubalgebra.mem_toSubmodule (L' := I.lieSubalgebra (B := k))).mpr h
  · intro d hd
    let x : I.lieSubalgebra (B := k) := ⟨d, hd⟩
    refine ⟨(I.quotientLieEquiv (B := k)).symm x, ?_⟩
    have h := congrArg Subtype.val ((I.quotientLieEquiv (B := k)).apply_symm_apply x)
    rw [I.quotientLieEquiv_apply_coe] at h
    simpa only [LieHom.coe_toLinearMap] using h

theorem range_normalizedTwistedBorelDifferential
    (I : HopfIdeal k H) (θ : H →ₐc[k] H) :
    LinearMap.range (normalizedTwistedBorelDifferential I θ) =
      LinearMap.range (LinearMap.id - (derivationCompLieHom (B := k) θ).toLinearMap) ⊔
        (I.lieSubalgebra (B := k)).toSubmodule := by
  rw [normalizedTwistedBorelDifferential_eq, LinearMap.range_coprod,
    range_quotientLieHom_eq_lieSubalgebra]

theorem compCounit_normalizedTwistedBorel_surjective
    (I : HopfIdeal k H) (θ : H →ₐc[k] H)
    (h : LinearMap.range (LinearMap.id - (derivationCompLieHom (B := k) θ).toLinearMap) ⊔
      (I.lieSubalgebra (B := k)).toSubmodule = ⊤) :
    Function.Surjective (Derivation.compCounit (normalizedTwistedBorelCoordinateMap I θ)
      (counit_comp_normalizedTwistedBorelCoordinateMap I θ)) := by
  have hs : Function.Surjective (normalizedTwistedBorelDifferential I θ) :=
    LinearMap.range_eq_top.mp ((range_normalizedTwistedBorelDifferential I θ).trans h)
  intro d
  obtain ⟨p, hp⟩ := hs d
  refine ⟨(Derivation.tensorProductLieEquiv (R := k) (H₁ := H)
    (H₂ := H ⧸ I.toIdeal) (B := k)).toLinearEquiv.symm p, ?_⟩
  exact hp

theorem derivationComp_mem_lieSubalgebra_of_stable
    (θ : H →ₐc[k] H) (I : HopfIdeal k H)
    (hs : ∀ a ∈ I.toIdeal, θ a ∈ I.toIdeal)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (hd : d ∈ I.lieSubalgebra (B := k)) :
    derivationComp (B := k) θ d ∈ I.lieSubalgebra (B := k) := by
  rw [HopfIdeal.mem_lieSubalgebra_iff] at hd ⊢
  intro a ha
  rw [derivationComp_apply]
  exact hd (θ a) (hs a ha)

theorem toConv_comp_normalizedTwistedBorelCoordinateMap
    (I : HopfIdeal k H) (θ : H →ₐc[k] H)
    (y : (H ⊗[k] (H ⧸ I.toIdeal)) →ₐ[k] k) :
    toConv (y.comp (normalizedTwistedBorelCoordinateMap I θ)) =
      toConv (y.comp (TauCeti.Bialgebra.TensorProduct.includeLeft
        (R := k) (H₁ := H) (H₂ := H ⧸ I.toIdeal)).toAlgHom) *
      AlgHom.mapDomain (A := k) (_root_.Bialgebra.Quotient.mkBialgHom I.toIdeal)
        (toConv (y.comp (TauCeti.Bialgebra.TensorProduct.includeRight
          (R := k) (H₁ := H) (H₂ := H ⧸ I.toIdeal)).toAlgHom)) *
      (AlgHom.mapDomain (A := k) θ
        (toConv (y.comp (TauCeti.Bialgebra.TensorProduct.includeLeft
          (R := k) (H₁ := H) (H₂ := H ⧸ I.toIdeal)).toAlgHom)))⁻¹ := by
  rw [show toConv (y.comp (normalizedTwistedBorelCoordinateMap I θ)) =
      (AlgHom.mapValue (H := H) y) (toConv (normalizedTwistedBorelCoordinateMap I θ))
      from by rw [AlgHom.mapValue_apply, ofConv_toConv]]
  rw [normalizedTwistedBorelCoordinateMap, toConv_ofConv, map_mul, map_mul]
  rw [map_inv (AlgHom.mapValue (H := H) y) _]
  simp only [AlgHom.mapValue_apply, AlgHom.mapDomain_apply]
  congr 2

end CFSG.LieType.AlgebraicGroups
