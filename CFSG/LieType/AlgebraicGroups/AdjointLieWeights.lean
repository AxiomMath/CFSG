module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Map
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TauCeti WithConv
open scoped TensorProduct

universe u v
variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H]

theorem adDerivation_pointInCounitAlgebra_eq_derivationComp_pointConjugation
    (g : WithConv (H →ₐ[R] R))
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    Derivation.adDerivation R (Derivation.pointInCounitAlgebra R g) d =
      derivationComp (B := R) (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom d := by
  let C := Bialgebra.CounitAlgebra R H R
  let e := Bialgebra.CounitAlgebra.algEquivSelf R H R
  have hscalar : (TrivSqZeroExt.inlAlgHom R C C).comp e.symm.toAlgHom =
      Algebra.ofId R (TrivSqZeroExt C C) := by
    apply AlgHom.ext
    intro r
    simpa only [Algebra.algebraMap_self, RingHom.id_apply, Algebra.ofId_apply] using
      ((TrivSqZeroExt.inlAlgHom R C C).comp e.symm.toAlgHom).commutes r
  have hlift : AlgHom.mapValue (H := H) (Algebra.ofId R (TrivSqZeroExt C C)) g =
      AlgHom.mapValue (H := H) (TrivSqZeroExt.inlAlgHom R C C)
        (Derivation.pointInCounitAlgebra R g) := by
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
    have hg : (Derivation.pointInCounitAlgebra R g).ofConv a = e.symm (g.ofConv a) := by
      rw [Derivation.pointInCounitAlgebra_apply]
      exact (Bialgebra.CounitAlgebra.algEquivSelf_symm_apply (R := R) (A := H) (B := R) _).symm
    rw [hg]
    exact (AlgHom.congr_fun hscalar (g.ofConv a)).symm
  apply Derivation.ext
  intro a
  have h := congrArg (fun ψ : tangentKer R H R => TrivSqZeroExt.snd (ψ.val.ofConv a))
    (tangentKerMap_derivationMulEquivTangentKer (B := R)
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom (Multiplicative.ofAdd d))
  rw [tangentKerMap_apply_val, TauCeti.HopfAlgebra.mapDomain_pointConjugationBialgEquiv,
    hlift, derivationMulEquivTangentKer_apply_snd] at h
  simp only [toAdd_ofAdd] at h
  exact (Derivation.snd_conjugate_tangentPoint d (Derivation.pointInCounitAlgebra R g) a).symm.trans h

theorem tangentScalarExtensionEquiv_one_tmul_eq_cotangentDualLieEquiv
    {k H : Type u} [CommRing k] [CommRing H] [HopfAlgebra k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Module.Projective k (Bialgebra.CotangentSpace k H)]
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := k) (1 ⊗ₜ[k] x) =
      Derivation.cotangentDualLieEquiv (R := k) (H := H) x := by
  apply Derivation.ext
  intro a
  rw [Derivation.tangentScalarExtensionEquiv_tmul_apply,
    Derivation.cotangentDualLieEquiv_apply, Derivation.cotangentLinearEquiv_apply_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, one_mul]
  rfl

theorem derivationComp_pointConjugation_of_mem_adjointWeightSpace
    {k H : Type u} [CommRing k] [CommRing H] [HopfAlgebra k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Module.Projective k (Bialgebra.CotangentSpace k H)]
    {M : Type*} [CommGroup M]
    (π : H →ₐc[k] MonoidAlgebra k M) (f : MonoidAlgebra k M →ₐ[k] k)
    {α : M} {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : x ∈ Derivation.adjointWeightSpace π α) :
    derivationComp (B := k) (TauCeti.HopfAlgebra.pointConjugationBialgEquiv
        (toConv (f.comp π.toAlgHom))).toBialgHom
      (Derivation.cotangentDualLieEquiv (R := k) (H := H) x) =
        f (MonoidAlgebra.single α 1) • Derivation.cotangentDualLieEquiv (R := k) (H := H) x := by
  let : Comodule k H (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
    Derivation.adjointComodule (R := k) (H := H)
  let g := toConv (f.comp π.toAlgHom)
  have hact := Derivation.endOfPoint_tmul_of_mem_adjointWeightSpace π f (1 : k) hx
  have h := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
    (CommAlgCat.of k k) g (1 ⊗ₜ[k] x)
  have htx : f (MonoidAlgebra.single α 1) ⊗ₜ[k] x =
      f (MonoidAlgebra.single α 1) • (1 ⊗ₜ[k] x) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hact, one_mul, htx, map_smul,
    tangentScalarExtensionEquiv_one_tmul_eq_cotangentDualLieEquiv x] at h
  exact (adDerivation_pointInCounitAlgebra_eq_derivationComp_pointConjugation g _).symm.trans h.symm

end CFSG.LieType.AlgebraicGroups
