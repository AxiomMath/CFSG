module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticB

open LinearMap (BilinForm)

universe v

variable {K : Type} [Field K] [Finite K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem linear_centralizer_pComponent_quasisimple
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = ℓ ^ f)
    (r : ℕ) (hr : 1 ≤ r) (hdim : Module.finrank K V = 2 * r)
    (B : BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, B (A x) (A y) = (μ : K) * B x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (p : ℕ) [Fact p.Prime] (L : Subgroup (symplecticOperatorCentralizer B A.toLinearMap))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  scalar_square_centralizer_pComponent_quasisimple hℓ hodd hf hcard hr hdim B hB hnd
    (LinearMap.GeneralLinearGroup.ofLinearEquiv A) hnonscalar d.ne_zero
    (LinearMap.ext hsquare) hsim p L hL

theorem projective_fixed_pComponent_quasisimple
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = ℓ ^ f)
    (r : ℕ) (hr : 1 ≤ r) (hdim : Module.finrank K V = 2 * r)
    (B : BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, B (A x) (A y) = (μ : K) * B x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (projectiveConjugation B A μ hsim)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  CatalogueBFixedCentralQuotient.quotientFixed_pComponent_quasisimple (scalarSigns B)
    (scalarSigns_central B) (similitudeConjugation B A μ hsim)
    (scalarSigns_invariant B A μ hsim) p
    (CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
      (fixedCentralizerEquiv B A μ hsim)
      (linear_centralizer_pComponent_quasisimple ℓ f hℓ hodd hf hcard r hr hdim B hB hnd
        A d μ hsquare hsim hnonscalar p)) L hL

omit [Finite K] [FiniteDimensional K V] in
theorem odd_symplectic_linear_involution_fixed_p_components
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = ℓ ^ f)
    (r : ℕ) (hr : 1 ≤ r) (hdim : Module.finrank K V = 2 * r)
    (B : BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, B (A x) (A y) = (μ : K) * B x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (symplecticOperatorCentralizer B A.toLinearMap),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (∀ p : ℕ, p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (projectiveConjugation B A μ hsim)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hℓ.pos f).ne')
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  constructor
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact linear_centralizer_pComponent_quasisimple ℓ f hℓ hodd hf hcard r hr hdim B hB hnd
      A d μ hsquare hsim hnonscalar p L hL
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact projective_fixed_pComponent_quasisimple ℓ f hℓ hodd hf hcard r hr hdim B hB hnd
      A d μ hsquare hsim hnonscalar p L hL

end CFSG.ComponentClassification.CatalogueBSymplecticB
