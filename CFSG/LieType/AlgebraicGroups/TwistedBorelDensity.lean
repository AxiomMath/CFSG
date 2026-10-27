module

public import CFSG.LieType.AlgebraicGroups.TwistedBorelDifferential
public import CFSG.LieType.AlgebraicGroups.PointedDifferentialDominance
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
public import TauCeti.Algebra.AlgebraicGroup.Smooth.Product
public import TauCeti.RingTheory.Smooth.GeometricallyReduced
public import TauCeti.RingTheory.Smooth.Regular

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TauCeti WithConv
open scoped TensorProduct

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem eq_zero_of_forall_twistedBorelPoints_eq_zero_of_range
    (M : FiniteTypeCommHopfAlgCat.{u,u} k) [Algebra.Smooth k M] [IsDomain M]
    (τ : M →ₐc[k] M) (B : HopfIdeal k M) (hB : HopfIdeal.IsBorelCandidate k M B)
    (b : WithConv (M →ₐ[k] k))
    (hb : b ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj B (CommAlgCat.of k k))
    (h : LinearMap.range (LinearMap.id - (derivationCompLieHom (B := k)
      (τ.comp (HopfAlgebra.pointConjugationBialgEquiv b).toBialgHom)).toLinearMap) ⊔
        (B.lieSubalgebra (B := k)).toSubmodule = ⊤)
    (p : M)
    (hp : ∀ (x c : WithConv (M →ₐ[k] k)),
      c ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj B (CommAlgCat.of k k) →
        (x * c * (AlgHom.mapDomain τ x)⁻¹).ofConv p = 0) : p = 0 := by
  let : Algebra.Smooth k (M ⧸ B.toIdeal) :=
    (smoothCommHopfAlgProperty_iff (FiniteTypeCommHopfAlgCat.quotient M B).obj).mp hB.smooth
  let A := M ⊗[k] (M ⧸ B.toIdeal)
  let : Algebra.Smooth k A :=
    (smoothCommHopfAlgProperty_iff (_root_.CommHopfAlgCat.of k A)).mp
      (smoothCommHopfAlgProperty.tensorProduct M.obj
        (FiniteTypeCommHopfAlgCat.quotient M B).obj
        ((smoothCommHopfAlgProperty_iff M.obj).mpr inferInstance) hB.smooth)
  let : IsRegularRing A := TauCeti.IsRegularRing.of_smooth (R := k)
  let : IsReduced A := TauCeti.isReduced_of_smooth k A
  let θ := τ.comp (HopfAlgebra.pointConjugationBialgEquiv b).toBialgHom
  let f := normalizedTwistedBorelCoordinateMap B θ
  let p' := HopfAlgebra.rightTranslationAlgEquiv b p
  have hs : Function.Surjective (Derivation.compCounit f
      (counit_comp_normalizedTwistedBorelCoordinateMap B θ)) :=
    compCounit_normalizedTwistedBorel_surjective B θ h
  have hp' : p' = 0 := by
    apply eq_zero_of_compCounit_surjective_of_forall_apply_eq_zero f
      (counit_comp_normalizedTwistedBorelCoordinateMap B θ) hs
    intro y
    let L := TauCeti.Bialgebra.TensorProduct.includeLeft
      (R := k) (H₁ := M) (H₂ := M ⧸ B.toIdeal)
    let R := TauCeti.Bialgebra.TensorProduct.includeRight
      (R := k) (H₁ := M) (H₂ := M ⧸ B.toIdeal)
    let x := toConv (y.comp L.toAlgHom)
    let c := toConv (y.comp R.toAlgHom)
    let cM := AlgHom.mapDomain (A := k) (_root_.Bialgebra.Quotient.mkBialgHom B.toIdeal) c
    have hc : cM ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj B (CommAlgCat.of k k) := by
      have hi := CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
        M.obj B (CommAlgCat.of k k) c
      have he : CommHopfAlgCat.quotientPointsHom M.obj B (CommAlgCat.of k k) c = cM := by
        apply WithConv.ext
        ext a
        rw [CommHopfAlgCat.quotientPointsHom_apply_apply, AlgHom.mapDomain_apply_apply]
        exact congrArg c.ofConv (DFunLike.congr_fun
          (_root_.Bialgebra.Quotient.mkBialgHom_toAlgHom (R := k) B.toIdeal) a).symm
      exact he ▸ hi
    have hself (g : WithConv (M →ₐ[k] k)) : AlgHom.mapValue (Algebra.ofId k k) g = g := by
      rw [AlgHom.mapValue_apply]
      apply WithConv.ext
      ext a
      simp only [AlgHom.comp_apply, Algebra.ofId_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    have hθ : AlgHom.mapDomain (A := k) θ x = b * AlgHom.mapDomain τ x * b⁻¹ := by
      rw [AlgHom.mapDomain_comp, MonoidHom.comp_apply,
        HopfAlgebra.mapDomain_pointConjugationBialgEquiv, hself]
    have he := congrArg (fun g : WithConv (M →ₐ[k] k) => g.ofConv p')
      (toConv_comp_normalizedTwistedBorelCoordinateMap B θ y)
    change y (f p') = (x * cM * (AlgHom.mapDomain θ x)⁻¹).ofConv p' at he
    have ht : p' = HopfAlgebra.rightTranslationAlgHom b p := by
      change (HopfAlgebra.rightTranslationAlgEquiv b).toAlgHom p = _
      rw [HopfAlgebra.rightTranslationAlgEquiv_toAlgHom]
    rw [ht, HopfAlgebra.ofConv_rightTranslationAlgHom, hθ] at he
    have hg : (x * cM * (b * AlgHom.mapDomain τ x * b⁻¹)⁻¹) * b =
        x * (cM * b) * (AlgHom.mapDomain τ x)⁻¹ := by group
    rw [hg] at he
    rw [ht]
    exact he.trans (hp x (cM * b) (mul_mem hc hb))
  apply (HopfAlgebra.rightTranslationAlgEquiv b).injective
  simpa only [map_zero] using hp'

end CFSG.LieType.AlgebraicGroups
