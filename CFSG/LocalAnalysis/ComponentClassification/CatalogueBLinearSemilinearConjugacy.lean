module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearNormalization
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerParameters
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearFaithfulness

public section

namespace CFSG.ComponentClassification.CatalogueBLinearSemilinear

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearField

universe u

theorem inner_field_conjugation (n : ℕ) (K : Type u) [Field K]
    (H : GL (Fin n) K) (sigma : K ≃+* K) :
    innerDiagonalAction n K H * pslFieldAut (Fin n) K sigma *
        (innerDiagonalAction n K H)⁻¹ =
      semilinearAction n K (H * glFieldAut (Fin n) K sigma H⁻¹) sigma := by
  have hright : semilinearAction n K H⁻¹ 1 = (innerDiagonalAction n K H)⁻¹ := by
    rw [semilinearAction_one_field, map_inv]
  have hproduct := semilinearAction_mul n K H H⁻¹ sigma 1
  rw [hright, mul_one] at hproduct
  exact hproduct

theorem field_involution_conjugacy (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hparameter : 3 ≤ n ∨ 4 ≤ Nat.card K)
    (htwo : (2 : K) ≠ 0) (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hne : sigma ≠ 1) (hsquare : semilinearAction n K A sigma ^ 2 = 1) :
    sigma ^ 2 = 1 ∧ ∃ H : GL (Fin n) K,
      semilinearAction n K A sigma =
        innerDiagonalAction n K H * pslFieldAut (Fin n) K sigma *
          (innerDiagonalAction n K H)⁻¹ := by
  obtain ⟨hsigma, c, hc⟩ := involution_scalar_cocycle n K hn hparameter A sigma hsquare
  obtain ⟨b, hcocycle, haction⟩ := exists_normalized_cocycle n (by omega) A sigma hsigma hne c hc
  let B := GeneralLinearGroup.scalar (Fin n) b * A
  obtain ⟨H, hH⟩ := CatalogueBLinearDescent.exists_gl_semilinear_coboundary n
    sigma hsigma hne htwo B hcocycle
  have hB : B = H * glFieldAut (Fin n) K sigma H⁻¹ := by
    rw [map_inv]
    exact (eq_mul_inv_iff_mul_eq).mpr hH
  refine ⟨hsigma, H, ?_⟩
  rw [← haction, inner_field_conjugation, ← hB]

theorem odd_linear_field_involution_conjugacy
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (hn : 2 ≤ n)
    (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : GL (Fin n) K) (sigma : K ≃+* K) (hne : sigma ≠ 1)
    (hsquare : semilinearAction n K A sigma ^ 2 = 1) :
    Even f ∧ (∀ x : K, sigma x = x ^ (p ^ (f / 2))) ∧
      ∃ H : GL (Fin n) K, semilinearAction n K A sigma =
        innerDiagonalAction n K H * pslFieldAut (Fin n) K sigma *
          (innerDiagonalAction n K H)⁻¹ := by
  have hodd : Odd (Nat.card K) := by rw [hcard]; exact hpodd.pow
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero
    (CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd)
  have hfaithful : 3 ≤ n ∨ 4 ≤ Nat.card K := by omega
  obtain ⟨hsigma, hconjugacy⟩ := field_involution_conjugacy n K hn hfaithful htwo
    A sigma hne hsquare
  obtain ⟨heven, hfrobenius, _⟩ := CatalogueBLinearTwoDescent.quadraticField_parameters
    K p f hp hcard sigma hsigma hne
  have _hpositive : 0 < f := by omega
  exact ⟨heven, hfrobenius, hconjugacy⟩

end

end CFSG.ComponentClassification.CatalogueBLinearSemilinear
