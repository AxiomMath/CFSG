module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBDescent

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticB

open CatalogueBLinearTwoDescent CatalogueBOrthogonalDescent CatalogueBAlternatingIsometry

universe u v

variable {K : Type u} [Field K] [Finite K] {V : Type v} [AddCommGroup V] [Module K V]
  [Module.Finite K V]

theorem semilinearCentralizer_pComponent_quasisimple
    (hodd : Odd (Nat.card K)) (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : 0 < Module.finrank K V) (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (tau0 : V ≃+ V) (mu lambda : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
    (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (semilinearSymplecticCentralizer B tau0))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Nontrivial V := (Module.finrank_pos_iff (R := K) (M := V)).mp hdim
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hfixed := square_scalar_fixed sigma tau0 (lambda : K) hsemi hsquare
  have hmu := square_multiplier_identity sigma hsigma B hnd tau0 (mu : K) (lambda : K)
    hform hsquare
  obtain ⟨b, c, hb, hc⟩ := exists_normalizing_units sigma hsigma hne mu lambda hfixed hmu
  let T := normalizedOperator tau0 b
  let hs := normalizedOperator_semilinear sigma tau0 b hsemi
  let hf := normalized_form_identity sigma B tau0 mu b c hform hc
  have hT := normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb
  let : Module.Finite (fixedSubfield K sigma) (fixedSubspace sigma T hs) := by
    obtain ⟨e, d, hd⟩ := exists_fixedSpace_basis sigma hsigma hne h2 T hT hs
    exact Module.Finite.of_basis d
  have hdimW : 2 ≤ Module.finrank (fixedSubfield K sigma) (fixedSubspace sigma T hs) := by
    rw [fixedSubspace_finrank sigma hsigma hne h2 T hT hs]
    obtain ⟨m, hm⟩ := even_finrank B hB hnd
    omega
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (originalSymplecticDescentEquiv sigma tau0 b hsemi B mu c hform hc hsigma hne h2 lambda
      hsquare hb)
    (isometry_pComponent_quasisimple _ (descendedBilinear_isAlt sigma T hs B c hf hB)
      (descendedBilinear_nondegenerate_of_isAlt sigma T hs B c hf hsigma hne h2 hT hB hnd)
      hdimW (CatalogueBOrthogonalFieldFixed.subfield_card_odd hodd (fixedSubfield K sigma)) p)
    L hL

theorem projective_semilinear_fixed_pComponent_quasisimple
    (hodd : Odd (Nat.card K)) (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : 0 < Module.finrank K V) (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (tau0 : V ≃+ V) (mu lambda : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
    (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x)
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup
      (projectiveSemilinearConjugation B sigma tau0 mu hsemi hform)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  CatalogueBFixedCentralQuotient.quotientFixed_pComponent_quasisimple (scalarSigns B)
    (scalarSigns_central B) (semilinearConjugation B sigma tau0 mu hsemi hform)
    (semilinear_scalarSigns_invariant B sigma tau0 mu hsemi hform) p
    (CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
      (semilinearFixedCentralizerEquiv B sigma tau0 mu hsemi hform)
      (semilinearCentralizer_pComponent_quasisimple hodd sigma hsigma hne hdim B hB hnd tau0
        mu lambda hsemi hform hsquare p)) L hL

theorem odd_symplectic_field_involution_fixed_p_components
    (hodd : Odd (Nat.card K)) (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : 0 < Module.finrank K V) (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (tau0 : V ≃+ V) (mu lambda : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
    (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x) :
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (semilinearSymplecticCentralizer B tau0),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup
      (projectiveSemilinearConjugation B sigma tau0 mu hsemi hform)),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) := by
  constructor
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact semilinearCentralizer_pComponent_quasisimple hodd sigma hsigma hne hdim B hB hnd
      tau0 mu lambda hsemi hform hsquare p L hL
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact projective_semilinear_fixed_pComponent_quasisimple hodd sigma hsigma hne hdim B hB
      hnd tau0 mu lambda hsemi hform hsquare p L hL

end CFSG.ComponentClassification.CatalogueBSymplecticB
