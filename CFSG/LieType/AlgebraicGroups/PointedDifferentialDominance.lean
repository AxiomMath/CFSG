module

public import CFSG.LieType.AlgebraicGroups.PointedDerivation
public import CFSG.Mathlib.RingTheory.CotangentInjective

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TauCeti _root_.Coalgebra

universe u v w
variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Bialgebra k H]
variable {A : Type w} [CommRing A] [Bialgebra k A]

theorem cotangent_injective_of_compCounit_surjective
    (f : H →ₐ[k] A)
    (hf : (_root_.Bialgebra.counitAlgHom k A).comp f =
      _root_.Bialgebra.counitAlgHom k H)
    (hsurj : Function.Surjective (Derivation.compCounit f hf)) :
    ∀ a ∈ RingHom.ker ((_root_.Bialgebra.counitAlgHom k A).comp f),
      f a ∈ RingHom.ker (_root_.Bialgebra.counitAlgHom k A) ^ 2 →
        a ∈ RingHom.ker ((_root_.Bialgebra.counitAlgHom k A).comp f) ^ 2 := by
  apply CFSG.cotangent_injective_of_forall_pointDerivation f
    (_root_.Bialgebra.counitAlgHom k A)
  intro D hD
  let eH := Bialgebra.CounitAlgebra.algEquivSelf k H k
  let eA := Bialgebra.CounitAlgebra.algEquivSelf k A k
  have hD' (a b : H) : D (a * b) = counit a * D b + counit b * D a := by
    have ha : (_root_.Bialgebra.counitAlgHom k A) (f a) = counit a := by
      simpa only [AlgHom.comp_apply, _root_.Bialgebra.counitAlgHom_apply] using
        DFunLike.congr_fun hf a
    have hb : (_root_.Bialgebra.counitAlgHom k A) (f b) = counit b := by
      simpa only [AlgHom.comp_apply, _root_.Bialgebra.counitAlgHom_apply] using
        DFunLike.congr_fun hf b
    rw [hD, ha, hb]
  let dH : Derivation k H (Bialgebra.CounitAlgebra k H k) :=
    Derivation.mk' (eH.symm.toLinearMap.comp D) (by
      intro a b
      apply eH.injective
      change eH (eH.symm (D (a * b))) =
        eH (a • eH.symm (D b) + b • eH.symm (D a))
      rw [AlgEquiv.apply_symm_apply, map_add]
      dsimp only [eH]
      simp only [Bialgebra.CounitAlgebra.algEquivSelf_smul,
        AlgEquiv.apply_symm_apply]
      exact hD' a b)
  have heq (a : H) : eH (dH a) = D a := by
    change eH (eH.symm (D a)) = D a
    exact eH.apply_symm_apply _
  obtain ⟨dA, hdA⟩ := hsurj dH
  refine ⟨eA.toLinearMap.comp (dA : A →ₗ[k] Bialgebra.CounitAlgebra k A k), ?_, ?_⟩
  · intro a b
    change eA (dA (a * b)) = counit a * eA (dA b) + counit b * eA (dA a)
    dsimp only [eA]
    rw [Bialgebra.CounitAlgebra.algEquivSelf_apply_mul]
    rfl
  · ext a
    change D a = eA (dA (f a))
    rw [← heq a, ← hdA, Derivation.compCounit_apply]
    dsimp only [eA, eH]
    rw [AlgEquiv.apply_symm_apply]

theorem eq_zero_of_compCounit_surjective_of_forall_apply_eq_zero
    [IsAlgClosed k] [IsDomain H] [IsNoetherianRing H] [IsRegularRing A]
    [Algebra.FiniteType k A] [IsReduced A] (f : H →ₐ[k] A)
    (hf : (_root_.Bialgebra.counitAlgHom k A).comp f =
      _root_.Bialgebra.counitAlgHom k H)
    (hsurj : Function.Surjective (Derivation.compCounit f hf)) {p : H}
    (hp : ∀ y : A →ₐ[k] k, y (f p) = 0) : p = 0 :=
  CFSG.eq_zero_of_cotangent_injective_at_of_forall_apply_eq_zero f
    (_root_.Bialgebra.counitAlgHom k A)
    (cotangent_injective_of_compCounit_surjective f hf hsurj) hp

end CFSG.LieType.AlgebraicGroups
