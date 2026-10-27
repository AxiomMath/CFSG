module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8s
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8r

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {K : Type} [Field K] {b c : K}

theorem exists_fusion_z1 [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2K : (2 : K) ≠ 0)
    (c₀ : K) [Fact (¬ IsSquare c₀)] (δ : (extension c₀)ˣ) (h2 : (2 : extension c₀) ≠ 0)
    (d : (extension c₀)ˣ) (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀))
    (hQd : ∀ v, Q8 K b c v = ((d : extension c₀) * OIL.qf (δ : extension c₀) (χ v)).re)
    (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
    (hχA : ∀ v, χ (A v) = (QuadraticAlgebra.omega : extension c₀) • χ v)
    (i : extension c₀) (hi : i * i = -1) (z : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
    (hz : ∀ v, z v = χ.symm ((OIU.Umat δ h2 (g1 (δ : extension c₀) i hi) :
      Matrix (Fin 4) (Fin 4) (extension c₀)) *ᵥ χ v)) :
    ∃ γ : orthogonalDerived (Q8 K b c), ∀ v, A (γ.val.val v) = γ.val.val (A (z v)) := by
  have hc₀ : c₀ ≠ 0 := fun h => (Fact.out : ¬ IsSquare c₀) (h ▸ ⟨0, by ring⟩)
  set ξ := xi c₀ d χ with hξ
  have hpol := polar_xi c₀ δ d χ hQd
  have hQu := Q_xi_hyp c₀ δ d χ hQd
  have q1 := Q_vu1 c₀ (Q8 K b c) ξ hQu
  have q2 := Q_vu2 c₀ (Q8 K b c) ξ hQu
  have q3 := Q_vw1 c₀ hc₀ (Q8 K b c) ξ hQu
  have q4 := Q_vw2 c₀ hc₀ (Q8 K b c) ξ hQu
  obtain ⟨hmem, hΩ⟩ := reflect_four_mem h2K hirr (vw1 c₀ ξ) (vw2 c₀ ξ) (vu1 c₀ ξ) (vu2 c₀ ξ)
    (by rw [q3]; exact h2K) (by rw [q4]; exact neg_ne_zero.mpr h2K) (by rw [q1]; exact hc₀)
    (by rw [q2]; exact neg_ne_zero.mpr hc₀)
    ⟨2 * c₀, by rw [q1, q2, q3, q4]; ring⟩
  refine ⟨⟨⟨_, hmem⟩, hΩ⟩, fun v => ?_⟩
  change A ((reflect (Q8 K b c) (vw1 c₀ ξ) * reflect (Q8 K b c) (vw2 c₀ ξ) *
      reflect (Q8 K b c) (vu1 c₀ ξ) * reflect (Q8 K b c) (vu2 c₀ ξ)) v) =
    (reflect (Q8 K b c) (vw1 c₀ ξ) * reflect (Q8 K b c) (vw2 c₀ ξ) *
      reflect (Q8 K b c) (vu1 c₀ ξ) * reflect (Q8 K b c) (vu2 c₀ ξ)) (A (z v))
  simp only [LinearEquiv.mul_apply]
  apply ξ.injective
  rw [xi_A c₀ d χ A hχA, reflect_four c₀ hc₀ (Q8 K b c) ξ hpol hQu h2K,
    reflect_four c₀ hc₀ (Q8 K b c) ξ hpol hQu h2K, xi_A c₀ d χ A hχA,
    xi_z1 c₀ δ h2 d χ i hi z hz]
  funext j
  fin_cases j
  all_goals simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, star_mul', star_neg]
  all_goals ext
  all_goals simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, hc₀]
  all_goals ring

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
