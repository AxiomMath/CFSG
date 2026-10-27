module

public import CFSG.LieType.AlgebraicGroups.SmoothTangentOpen
public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct

section Tangent

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] [Algebra A k] [IsScalarTower k A k]

theorem finrank_tangentSpace_eq_finrank_tensorProduct (x : A →ₐ[k] k)
    (hx : ∀ a, algebraMap A k a = x a) :
    Module.finrank k (TangentSpace k A x) = Module.finrank k (k ⊗[A] Ω[A⁄k]) := by
  let e₁ : Module.Dual k (k ⊗[A] Ω[A⁄k]) ≃ₗ[k] (Ω[A⁄k] →ₗ[A] k) :=
    (LinearMap.liftBaseChangeEquiv k).symm
  let e₂ : (Ω[A⁄k] →ₗ[A] k) ≃ₗ[k] Derivation k A k :=
    (KaehlerDifferential.linearMapEquivDerivation k A).restrictScalars k
  let f₃ : Derivation k A k →ₗ[k] TangentSpace k A x :=
    { toFun := derivationToTangent x hx
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e₃ := LinearEquiv.ofBijective f₃ (derivationToTangent_bijective x hx)
  rw [← e₃.finrank_eq, ← e₂.finrank_eq, ← e₁.finrank_eq, Subspace.dual_finrank_eq]

end Tangent

theorem finrank_kaehlerDifferential_eq_trdeg (k K : Type) [Field k] [Field K] [Algebra k K]
    [PerfectField k] [Algebra.EssFiniteType k K] :
    (Module.finrank K Ω[K⁄k] : Cardinal) = Algebra.trdeg k K := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hx : AlgebraicIndependent k ((↑) : s → K) := hs.1
  let P := MvPolynomial s k
  let F := FractionRing P
  let i : F →ₐ[k] K := IsFractionRing.liftAlgHom (algebraicIndependent_iff_injective_aeval.2 hx)
  let : Algebra F K := (i : F →+* K).toAlgebra
  let : Algebra P K := ((algebraMap F K).comp (algebraMap P F)).toAlgebra
  have : IsScalarTower P F K := .of_algebraMap_eq' rfl
  have : IsScalarTower k F K := .of_algebraMap_eq fun c => (i.commutes c).symm
  have : IsScalarTower k P K := .of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k F K, IsScalarTower.algebraMap_apply k P F]
    rfl
  have hrange : IntermediateField.adjoin k (s : Set K) =
      IntermediateField.adjoin k (Set.range ((↑) : s → K)) := by
    rw [Subtype.range_coe_subtype]
    rfl
  have : Algebra.IsSeparable F K := by
    refine Algebra.IsSeparable.of_equiv_equiv
      ((IntermediateField.equivOfEq hrange).toRingEquiv.trans hx.aevalEquivField.symm.toRingEquiv)
      (RingEquiv.refl K) ?_
    ext z
    exact hx.lift_reprField _
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  have : Algebra.FormallyEtale P F := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  have : Algebra.FormallyEtale P K := Algebra.FormallyEtale.comp P F K
  let b : Module.Basis s K Ω[K⁄k] := IsBaseChange.basis
    (KaehlerDifferential.mvPolynomialBasis k s)
    (KaehlerDifferential.isBaseChange_of_formallyEtale k P K)
  rw [Module.finrank_eq_card_basis b, ← hs.cardinalMk_eq_trdeg, Cardinal.mk_fintype]

theorem finrank_tangentSpace_eq_trdeg {k A : Type} [Field k] [PerfectField k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [Algebra.Smooth k A] [IsDomain A] (x : A →ₐ[k] k) :
    (Module.finrank k (TangentSpace k A x) : Cardinal) = Algebra.trdeg k (FractionRing A) := by
  let : Algebra A k := (x : A →+* k).toAlgebra
  have : IsScalarTower k A k := .of_algebraMap_eq fun c => (x.commutes c).symm
  let P := RingHom.ker (algebraMap A k)
  have : P.IsPrime := RingHom.ker_isPrime _
  let g : P.ResidueField →ₐ[A] k := Ideal.ResidueField.liftₐ P (Algebra.ofId A k) le_rfl
    fun s hs => isUnit_iff_ne_zero.2 hs
  let : Algebra P.ResidueField k := g.toAlgebra
  have : IsScalarTower A P.ResidueField k := .of_algebraMap_eq fun a => (g.commutes a).symm
  have h₁ : Module.finrank k (TangentSpace k A x) = Module.finrank A Ω[A⁄k] := by
    rw [finrank_tangentSpace_eq_finrank_tensorProduct x fun _ => rfl,
      ← (AlgebraTensorModule.cancelBaseChange A P.ResidueField k k Ω[A⁄k]).finrank_eq,
      Module.finrank_baseChange]
    exact Ideal.finrank_fiber_eq_finrank P
  have h₂ : Module.finrank (FractionRing A) Ω[FractionRing A⁄k] = Module.finrank A Ω[A⁄k] := by
    have : Algebra.FormallyEtale A (FractionRing A) :=
      Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
    exact (KaehlerDifferential.isBaseChange_of_formallyEtale k A (FractionRing A)).finrank_eq
  rw [h₁, ← h₂]
  exact finrank_kaehlerDifferential_eq_trdeg k (FractionRing A)

end CFSG.LieType.AlgebraicGroups
