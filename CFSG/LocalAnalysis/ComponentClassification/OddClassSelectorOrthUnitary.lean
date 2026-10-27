module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthExt
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSU

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth_unitary_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (hnsq : ¬ IsSquare (d : K)) (hμ : (μ : K) / (d : K) = -1)
    {Y : Subgroup (V ≃ₗ[K] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X) : False := by
  classical
  obtain ⟨-, -, -, hns4⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ A d μ hsquare hsim hnonscalar
  have h4 := hns4 hnsq
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let : Field (scalarAlgebra A.toLinearMap) := scalarField A.toLinearMap d hnsq
    (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare)
  let : Module (scalarAlgebra A.toLinearMap) V := evaluationModule A.toLinearMap
  obtain ⟨⟨-, hfin, -, -, -, -, -, -, hcard, -, hinv, hne1, -, -, hpow, -, -, -, -, hfinE,
    hfinrank, -⟩, -, hneg⟩ := h4
  obtain ⟨hsym, hnd, -, -, -, -, eU, -, -, -, -⟩ := hneg hμ
  have := hfin
  have : FiniteDimensional (scalarAlgebra A.toLinearMap) V := hfinE
  obtain ⟨-, hY₁, ⟨eY⟩⟩ := isComponent_operatorCentralizer hY
  have hL' := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent eU hY₁
  let e1 := (((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
    (orthogonalOperatorCentralizer Q A.toLinearMap)).equivMapOfInjective eU.toMonoidHom
      eU.injective).symm.trans eY
  refine unitary_component_false hℓ hℓ2 he hcard (by omega) _ hsym hnd ?_ ?_ (fun z => hpow z)
    hL' (σ.comp e1.toMonoidHom) (hσs.comp e1.surjective)
    (ker_comp_le_center e1.toMonoidHom e1.injective σ hσk) hs
  · refine RingEquiv.ext fun z => ?_
    rw [pow_two, RingAut.mul_apply, RingAut.one_apply, AlgEquiv.coe_toRingEquiv]
    exact hinv z
  · intro h1
    apply hne1
    refine AlgEquiv.ext fun z => ?_
    have h2 := DFunLike.congr_fun h1 z
    rw [RingAut.one_apply, AlgEquiv.coe_toRingEquiv] at h2
    rw [h2, AlgEquiv.one_apply]

end CFSG.ComponentClassification.OddClassSelector
