module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8f
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUj

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {K : Type} [Field K] {b c : K}

theorem y_neg_one (c₀ : K) [Fact (¬ IsSquare c₀)] (δ : (extension c₀)ˣ)
    (hδ : ¬ IsSquare (δ : extension c₀)) (h2 : (2 : extension c₀) ≠ 0)
    (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀))
    (y : SpecialLinearGroup (Fin 2) (extension (δ : extension c₀)) →*
      orthogonalDerived (Q8 K b c))
    (hy : ∀ h v, (y h).val.val v =
      χ.symm ((OIU.Umat δ h2 h : Matrix (Fin 4) (Fin 4) (extension c₀)) *ᵥ χ v)) :
    y (-1) = 1 := by
  have hU : OIU.Umat δ h2 (-1) = 1 :=
    (OIU.rowOHom_eq_one_iff h2 hδ (hermitianCoordinates (δ : extension c₀) h2) (-1)).mpr
      (Or.inr rfl)
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [hy, hU, Units.val_one, Matrix.one_mulVec, LinearEquiv.symm_apply_apply]
  rfl

theorem eq_scalar_of_mulVec4 {k : Type*} [Field k] {U : GL (Fin 4) k} (u : kˣ)
    (h : ∀ w, U.val *ᵥ w = (u : k) • w) : U = GeneralLinearGroup.scalar (Fin 4) u := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  simp

theorem mul_self_eq_neg_one [Finite K] (hQ0 : ∃ v, Q8 K b c v ≠ 0) (hodd : Odd (Nat.card K))
    (c₀ : K) [Fact (¬ IsSquare c₀)] (δ : (extension c₀)ˣ)
    (hδ : ¬ IsSquare (δ : extension c₀)) (h2 : (2 : extension c₀) ≠ 0)
    (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀))
    (y : SpecialLinearGroup (Fin 2) (extension (δ : extension c₀)) →*
      orthogonalDerived (Q8 K b c))
    (hy : ∀ h v, (y h).val.val v =
      χ.symm ((OIU.Umat δ h2 h : Matrix (Fin 4) (Fin 4) (extension c₀)) *ᵥ χ v))
    (h : SpecialLinearGroup (Fin 2) (extension (δ : extension c₀)))
    (hord : orderOf ((theta K b c hQ0).symm (QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) (y h))) = 2) :
    h * h = -1 := by
  set N := (scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c)) with hN
  have := finite_extension c₀
  have : Fact (¬ IsSquare (δ : extension c₀)) := ⟨hδ⟩
  have hEodd : Odd (Nat.card (extension c₀)) := by rw [card_extension]; exact hodd.pow
  have h1 : (QuotientGroup.mk' N (y h)) ^ 2 = 1 := by
    have e := congrArg (theta K b c hQ0)
      (pow_orderOf_eq_one ((theta K b c hQ0).symm (QuotientGroup.mk' N (y h))))
    rwa [hord, map_pow, MulEquiv.apply_symm_apply, map_one] at e
  have hsq : QuotientGroup.mk' N (y (h * h)) = 1 := by
    rw [map_mul, map_mul, ← pow_two, h1]
  have hmem : (y (h * h)).val ∈ scalarSigns (Q8 K b c) :=
    (QuotientGroup.eq_one_iff (N := N) _).mp hsq
  obtain ⟨ε, hε⟩ : ∃ ε : (extension c₀)ˣ, ∀ w, ((OIU.Umat δ h2 (h * h) :
      Matrix (Fin 4) (Fin 4) (extension c₀))) *ᵥ w = (ε : extension c₀) • w := by
    rcases (mem_scalarSigns_iff (Q8 K b c) _).mp hmem with he | he
    · refine ⟨1, fun w => ?_⟩
      have e := hy (h * h) (χ.symm w)
      rw [he, LinearEquiv.apply_symm_apply] at e
      apply χ.symm.injective
      rw [← e, Units.val_one, one_smul]
      rfl
    · refine ⟨-1, fun w => ?_⟩
      have e := hy (h * h) (χ.symm w)
      rw [he, LinearEquiv.apply_symm_apply, QuadraticMap.coe_negOrthogonal] at e
      apply χ.symm.injective
      rw [← e, Units.val_neg, Units.val_one, neg_one_smul, map_neg]
      rfl
  have hU := eq_scalar_of_mulVec4 ε hε
  rcases OIU.eq_one_or_neg_one_of_rowOHom_scalar hEodd hδ
    (hermitianCoordinates (δ : extension c₀) h2) (h * h) ε hU with hh | hh
  · exfalso
    have hE2 : (2 : extension (δ : extension c₀)) ≠ 0 :=
      OIL.two_ne_zero_ext (δ : extension c₀) h2
    have hpm : h = 1 ∨ h = -1 := by
      by_cases h1' : h = 1
      · exact Or.inl h1'
      · right
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
        exact CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq hE2 h (by rw [pow_two, hh]) h1'
    have hy1 : y h = 1 := by
      rcases hpm with rfl | rfl
      · exact map_one y
      · exact y_neg_one c₀ δ hδ h2 χ y hy
    rw [hy1, map_one (QuotientGroup.mk' N), map_one (theta K b c hQ0).symm, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · exact hh

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
