module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedConjugation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedBranches

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

open CatalogueBOrthogonalScalarSquare

universe u v

variable {K : Type u} [Field K] [Finite K] {V : Type v}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem original_centralizer_pComponent_quasisimple
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (_hf : 1 ≤ f)
    (hcard : Nat.card K = ℓ ^ f) (hn : 2 ≤ Module.finrank K V)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (orthogonalOperatorCentralizer Q A.toLinearMap))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank K V by omega)
  have hKodd : Odd (Nat.card K) := by
    rw [hcard]
    exact (hℓ.odd_of_ne_two hodd).pow
  exact scalar_square_centralizer_pComponent_quasisimple hKodd Q hQ A d μ
    hsquare (polar_similarity Q A μ hsim) hnonscalar p L hL

theorem projective_fixed_pComponent_quasisimple
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card K = ℓ ^ f) (hn : 2 ≤ Module.finrank K V)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (projectiveConjugation Q A μ hsim)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have hfixed : ∀ M : Subgroup (FixedCommutingProduct.fixedSubgroup
      (similarityConjugation Q A μ hsim)),
      CFSG.IsPComponent p M → CFSG.IsQuasisimple M :=
    CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
      (fixedCentralizerEquiv Q A μ hsim)
      (original_centralizer_pComponent_quasisimple ℓ f hℓ hodd hf hcard hn Q hQ
        A d μ hsquare hsim hnonscalar p)
  exact normal_central_quotient_fixed_pComponent_quasisimple
    (orthogonalDerived Q) (scalarSigns Q) (scalarSigns_central Q)
    (similarityConjugation Q A μ hsim) (orthogonalDerived_invariant Q A μ hsim)
    (scalarSigns_invariant Q A μ hsim) p hfixed L hL

theorem odd_orthogonal_linear_involution_fixed_p_components
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card K = ℓ ^ f) (hn : 2 ≤ Module.finrank K V)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (orthogonalOperatorCentralizer Q A.toLinearMap),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (∀ p : ℕ, p.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (projectiveConjugation Q A μ hsim)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L) := by
  constructor
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact original_centralizer_pComponent_quasisimple ℓ f hℓ hodd hf hcard hn Q hQ
      A d μ hsquare hsim hnonscalar p L hL
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact projective_fixed_pComponent_quasisimple ℓ f hℓ hodd hf hcard hn Q hQ
      A d μ hsquare hsim hnonscalar p L hL

end CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
