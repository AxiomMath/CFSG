module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFieldFixedConjugation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFieldFixedPolarization

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFieldFixed

open CatalogueBOrthogonalDescent CatalogueBOrthogonalLinearFixed

universe u v

variable {K : Type u} [Field K] [Finite K] {V : Type v}
  [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem projective_semilinear_fixed_pComponent_quasisimple
    (hodd : Odd (Nat.card K)) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : 0 < Module.finrank K V) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (tau0 : V ≃+ V) (mu lambda : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x))
    (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x)
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup
      (projectiveSemilinearConjugation Q sigma tau0 mu hsemi hsim)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have hfixed : ∀ M : Subgroup (FixedCommutingProduct.fixedSubgroup
      (semilinearConjugation Q sigma tau0 mu hsemi hsim)),
      CFSG.IsPComponent p M → CFSG.IsQuasisimple M :=
    CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
      (semilinearFixedCentralizerEquiv Q sigma tau0 mu hsemi hsim)
      (semilinearCentralizer_pComponent_quasisimple hodd sigma hsigma hne hdim
        Q hQ tau0 mu lambda hsemi hsim hsquare p)
  exact normal_central_quotient_fixed_pComponent_quasisimple
    (orthogonalDerived Q) (scalarSigns Q) (scalarSigns_central Q)
    (semilinearConjugation Q sigma tau0 mu hsemi hsim)
    (semilinear_orthogonalDerived_invariant Q sigma tau0 mu hsemi hsim)
    (semilinear_scalarSigns_invariant Q sigma tau0 mu hsemi hsim) p hfixed L hL

theorem odd_orthogonal_field_involution_fixed_p_components
    (hodd : Odd (Nat.card K)) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : 0 < Module.finrank K V) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (tau0 : V ≃+ V) (mu lambda : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x))
    (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x) :
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (semilinearOrthogonalCentralizer Q tau0),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup
      (projectiveSemilinearConjugation Q sigma tau0 mu hsemi hsim)),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) := by
  constructor
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact semilinearCentralizer_pComponent_quasisimple hodd sigma hsigma hne hdim
      Q hQ tau0 mu lambda hsemi hsim hsquare p L hL
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact projective_semilinear_fixed_pComponent_quasisimple hodd sigma hsigma hne hdim
      Q hQ tau0 mu lambda hsemi hsim hsquare p L hL

end CFSG.ComponentClassification.CatalogueBOrthogonalFieldFixed
