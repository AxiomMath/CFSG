module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8j

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {K : Type} [Field K] {b c : K}

theorem trace_scalar_mul (u : Kˣ) (X : GL (Fin (2 * 4)) K) :
    ((GeneralLinearGroup.scalar (Fin (2 * 4)) u * X : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace =
      (u : K) * (X : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul]

theorem not_anticomm [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hQ0 : ∃ v, Q8 K b c v ≠ 0)
    (ψ : MulAut (G0 K b c)) (g : similarityPairs (Q8 K b c))
    (hg : matrixProjectiveConjugationHom (Q8 K b c) g = MulAut.congr (psiC K b c) ψ)
    (hg1 : g.val.right = 1) (Y : GL (Fin (2 * 4)) K)
    (c₀ : K) [Fact (¬ IsSquare c₀)] (δ : (extension c₀)ˣ) (h2 : (2 : extension c₀) ≠ 0)
    (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀))
    (hχA : ∀ v, χ (Y.val *ᵥ v) = (QuadraticAlgebra.omega : extension c₀) • χ v)
    (y : SpecialLinearGroup (Fin 2) (extension (δ : extension c₀)) →*
      orthogonalDerived (Q8 K b c))
    (hy : ∀ h v, (y h).val.val v =
      χ.symm ((OIU.Umat δ h2 h : Matrix (Fin 4) (Fin 4) (extension c₀)) *ᵥ χ v))
    (hfix : ∀ h, ψ ((theta K b c hQ0).symm (QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) (y h))) =
      (theta K b c hQ0).symm (QuotientGroup.mk' _ (y h)))
    (hanti : g.val.left * Y = GeneralLinearGroup.scalar (Fin (2 * 4)) (-1) * (Y * g.val.left)) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hK
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have h2K : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hc₀ : c₀ ≠ 0 := fun h => (Fact.out : ¬ IsSquare c₀) (h ▸ ⟨0, by ring⟩)
  have := finite_extension c₀
  have : Fintype (extension c₀) := Fintype.ofFinite _
  have hqE : Fintype.card (extension c₀) % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, card_extension, hK, ← pow_mul]
    exact Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  obtain ⟨a, a', ha⟩ := OFL.exists_norm_eq hqE δ.ne_zero (QuadraticAlgebra.omega : extension c₀)
  have hW := congrArg Subtype.val (conj_gT hQ0 ψ g hg c₀ δ y hfix ⟨a, a'⟩)
  rw [matrixDerivedConjugation_val, hg1, map_one, MulAut.one_apply] at hW
  set W := ((derivedEquiv (Q8 K b c)).symm (y (gT (δ : extension c₀) ⟨a, a'⟩))).val with hWdef
  have hYW : g.val.left * (Y * W) * g.val.left⁻¹ =
      GeneralLinearGroup.scalar (Fin (2 * 4)) (-1) * (Y * W) := by
    calc g.val.left * (Y * W) * g.val.left⁻¹ =
          (g.val.left * Y) * (g.val.left⁻¹ * (g.val.left * W * g.val.left⁻¹)) := by group
      _ = GeneralLinearGroup.scalar (Fin (2 * 4)) (-1) * (Y * g.val.left) *
          (g.val.left⁻¹ * W) := by rw [hanti, hW]
      _ = _ := by group
  have htr := congrArg
    (fun X : GL (Fin (2 * 4)) K => (X : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace) hYW
  rw [trace_scalar_mul, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, Units.inv_mul,
    one_mul, Units.val_neg, Units.val_one] at htr
  have h0 : ((Y * W : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace = 0 := by
    have h3 : (2 : K) *
        ((Y * W : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace = 0 := by
      rw [Units.val_mul]
      linear_combination htr
    exact (mul_eq_zero.mp h3).resolve_left h2K
  rw [Units.val_mul, hWdef, trace_A_derived c₀ χ _ Y hχA _ (hy _),
    OIL.trace_rowOHom_gT δ h2 (hermitianCoordinates (δ : extension c₀) h2) ⟨a, a'⟩] at h0
  change 2 * (c₀ * (a ^ 2 - (δ : extension c₀) * a' ^ 2).im) = 0 at h0
  rw [ha, QuadraticAlgebra.im_omega, mul_one] at h0
  exact (mul_ne_zero h2K hc₀) h0

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
