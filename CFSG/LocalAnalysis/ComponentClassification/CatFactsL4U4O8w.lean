module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8v
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8t
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8u

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {K : Type} [Field K] {b c : K}

theorem exists_sqrt_neg_one [Finite K] (hodd : Odd (Nat.card K)) (c₀ : K)
    [Fact (¬ IsSquare c₀)] : ∃ i : extension c₀, i * i = -1 := by
  have := finite_extension c₀
  let : Fintype (extension c₀) := Fintype.ofFinite _
  have h4 : Fintype.card (extension c₀) % 4 ≠ 3 := by
    rw [← Nat.card_eq_fintype_card, card_extension]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring]
    omega
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.mpr h4
  exact ⟨i, hi.symm⟩

theorem comm_conj {G : Type*} [Group G] (A Y G' Z₁ : G) (hAY : A * Y = Y * A)
    (hAG : A * G' = G' * (A * Z₁)) :
    A * (Y * G' * Y⁻¹) = (Y * G' * Y⁻¹) * (A * (Y * Z₁ * Y⁻¹)) := by
  calc A * (Y * G' * Y⁻¹) = (A * Y) * G' * Y⁻¹ := by group
    _ = Y * (A * G') * Y⁻¹ := by rw [hAY]; group
    _ = Y * (G' * (A * Z₁)) * Y⁻¹ := by rw [hAG]
    _ = (Y * G' * Y⁻¹) * ((Y * A) * Z₁ * Y⁻¹) := by group
    _ = (Y * G' * Y⁻¹) * ((A * Y) * Z₁ * Y⁻¹) := by rw [hAY]
    _ = (Y * G' * Y⁻¹) * (A * (Y * Z₁ * Y⁻¹)) := by group

theorem outer_fus_O8 [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hodd : Odd (Nat.card K)) (hQ0 : ∃ v, Q8 K b c v ≠ 0) (φ : MulAut (G0 K b c))
    (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ : Kˣ)
    (hsim : ∀ x, Q8 K b c (A x) = (μ : K) * Q8 K b c x)
    (hφ : ∀ x, theta K b c hQ0 (φ x) =
      projectiveConjugation (Q8 K b c) A μ hsim (theta K b c hQ0 x))
    (c₀ : K) [Fact (¬ IsSquare c₀)] (δ : (extension c₀)ˣ)
    (hδ : ¬ IsSquare (δ : extension c₀)) (h2 : (2 : extension c₀) ≠ 0) (d : (extension c₀)ˣ)
    (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀))
    (y : SpecialLinearGroup (Fin 2) (extension (δ : extension c₀)) →*
      orthogonalDerived (Q8 K b c))
    (hχA : ∀ v, χ (A v) = (QuadraticAlgebra.omega : extension c₀) • χ v)
    (hQd : ∀ v, Q8 K b c v = ((d : extension c₀) * OIL.qf (δ : extension c₀) (χ v)).re)
    (hy : ∀ h v, (y h).val.val v =
      χ.symm ((OIU.Umat δ h2 h : Matrix (Fin 4) (Fin 4) (extension c₀)) *ᵥ χ v))
    (J' : Subgroup (G0 K b c))
    (hJy : ∀ x, x ∈ J' ↔ ∃ h, QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) (y h) =
        theta K b c hQ0 x) :
    ∀ ζ ∈ J', orderOf ζ = 2 → ∃ γ : G0 K b c,
      (MulAut.conj γ)⁻¹ * φ * MulAut.conj γ = φ * MulAut.conj ζ := by
  intro ζ hζ hord
  have h2K : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨h, hh⟩ := (hJy ζ).mp hζ
  have hζ' : ζ = (theta K b c hQ0).symm (QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) (y h)) := by
    rw [hh, MulEquiv.symm_apply_apply]
  rw [hζ'] at hord
  have hsq := mul_self_eq_neg_one hQ0 hodd c₀ δ hδ h2 χ y hy h hord
  obtain ⟨i, hi⟩ := exists_sqrt_neg_one hodd c₀
  have := finite_extension c₀
  let : Fintype (extension c₀) := Fintype.ofFinite _
  have hqE : Fintype.card (extension c₀) % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, card_extension]
    exact Nat.odd_iff.mp hodd.pow
  obtain ⟨a₁, ha₁⟩ := OIL.exists_conj_g0 hqE h2 hδ h hsq
  obtain ⟨a₂, ha₂⟩ := OIL.exists_conj_g0 hqE h2 hδ (g1 (δ : extension c₀) i hi)
    (g1_mul_self (δ : extension c₀) i hi)
  have hconj : h = (a₁ * a₂⁻¹) * g1 (δ : extension c₀) i hi * (a₁ * a₂⁻¹)⁻¹ := by
    have e1 : h = a₁ * OIL.g0 (δ : extension c₀) * a₁⁻¹ := by
      rw [ha₁]; group
    have e2 : OIL.g0 (δ : extension c₀) = a₂⁻¹ * g1 (δ : extension c₀) i hi * a₂ := by
      rw [mul_assoc, ← ha₂]; group
    rw [e1, e2]
    group
  obtain ⟨γ₁, hγ₁⟩ := exists_fusion_z1 hirr h2K c₀ δ h2 d χ hQd A hχA i hi
    (y (g1 (δ : extension c₀) i hi)).val.val (hy _)
  have hAc : ∀ v, A ((y (a₁ * a₂⁻¹)).val.val v) = (y (a₁ * a₂⁻¹)).val.val (A v) := fun v => by
    apply χ.injective
    rw [hχA, hy, hy, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hχA,
      Matrix.mulVec_smul]
  have hmain := comm_conj A (y (a₁ * a₂⁻¹)).val.val γ₁.val.val
    (y (g1 (δ : extension c₀) i hi)).val.val (LinearEquiv.ext hAc) (LinearEquiv.ext hγ₁)
  have hyh : (y h).val.val = (y (a₁ * a₂⁻¹)).val.val * (y (g1 (δ : extension c₀) i hi)).val.val *
      ((y (a₁ * a₂⁻¹)).val.val)⁻¹ := by
    rw [hconj, map_mul, map_mul, map_inv]
    rfl
  rw [hζ']
  refine ⟨(theta K b c hQ0).symm (QuotientGroup.mk' _
    (y (a₁ * a₂⁻¹) * γ₁ * (y (a₁ * a₂⁻¹))⁻¹)), ?_⟩
  refine fusion_of_comm hQ0 φ A μ hsim hφ (y (a₁ * a₂⁻¹) * γ₁ * (y (a₁ * a₂⁻¹))⁻¹) (y h)
    fun v => ?_
  have e := LinearEquiv.congr_fun hmain v
  rw [← hyh] at e
  exact e

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
