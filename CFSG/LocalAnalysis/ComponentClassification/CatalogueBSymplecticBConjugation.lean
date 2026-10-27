module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionCommutant
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientAlgebra

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticB

open LinearMap (BilinForm)
open CatalogueBAlternatingIsometry CatalogueBProjectiveInvolution

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

@[expose] def negIsometry (B : BilinForm K V) : isometryGroup B :=
  ⟨LinearEquiv.neg K, (mem_isometryGroup_iff B _).mpr fun x y => by
    simp only [LinearEquiv.coe_neg, Pi.neg_apply, id_eq, map_neg, LinearMap.neg_apply,
      neg_neg]⟩

theorem negIsometry_apply (B : BilinForm K V) (x : V) : (negIsometry B).val x = -x := rfl

theorem negIsometry_mul_self (B : BilinForm K V) : negIsometry B * negIsometry B = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change -(-x) = x
  exact neg_neg x

@[expose] def scalarSigns (B : BilinForm K V) : Subgroup (isometryGroup B) where
  carrier := {g | g = 1 ∨ g = negIsometry B}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro g h (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (negIsometry_mul_self B)
  inv_mem' := by
    rintro g (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right (negIsometry_mul_self B))

theorem mem_scalarSigns_iff (B : BilinForm K V) (g : isometryGroup B) :
    g ∈ scalarSigns B ↔ g = 1 ∨ g = negIsometry B := Iff.rfl

theorem negIsometry_central (B : BilinForm K V) :
    negIsometry B ∈ Subgroup.center (isometryGroup B) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (-x) = -(g.val x)
  exact map_neg g.val x

theorem scalarSigns_central (B : BilinForm K V) :
    scalarSigns B ≤ Subgroup.center (isometryGroup B) := by
  rintro z (rfl | rfl)
  · exact Subgroup.one_mem _
  · exact negIsometry_central B

instance scalarSigns_normal (B : BilinForm K V) : (scalarSigns B).Normal :=
  Subgroup.normal_of_le_center (scalarSigns_central B)

abbrev projectiveSymplectic (B : BilinForm K V) := isometryGroup B ⧸ scalarSigns B

theorem scalarSigns_map_eq (B : BilinForm K V) (ψ : MulAut (isometryGroup B))
    (hψ : ψ (negIsometry B) = negIsometry B) :
    (scalarSigns B).map ψ.toMonoidHom = scalarSigns B := by
  have hfix : ∀ z ∈ scalarSigns B, ψ z = z := by
    rintro z (rfl | rfl)
    · exact map_one ψ
    · exact hψ
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change ψ w ∈ scalarSigns B
    rw [hfix w hw]
    exact hw
  · intro hz
    exact ⟨z, hz, hfix z hz⟩

@[expose] def symplecticOperatorCentralizer (B : BilinForm K V) (T : Module.End K V) :
    Subgroup (isometryGroup B) :=
  (operatorCentralizer T).comap (isometryGroup B).subtype

theorem mem_symplecticOperatorCentralizer_iff (B : BilinForm K V) (T : Module.End K V)
    (g : isometryGroup B) :
    g ∈ symplecticOperatorCentralizer B T ↔ ∀ x, g.val (T x) = T (g.val x) := Iff.rfl

theorem inverse_similitude (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) (x y : V) :
    B (A.symm x) (A.symm y) = (↑μ⁻¹ : K) * B x y := by
  have h := hsim (A.symm x) (A.symm y)
  rw [A.apply_symm_apply, A.apply_symm_apply] at h
  rw [h, Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero μ), one_mul]

theorem similitude_conjugation_preserves (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) (g : isometryGroup B) :
    A * g.val * A⁻¹ ∈ isometryGroup B := by
  apply (mem_isometryGroup_iff B _).mpr
  intro x y
  change B (A (g.val (A.symm x))) (A (g.val (A.symm y))) = B x y
  rw [hsim, (mem_isometryGroup_iff B g.val).mp g.property, inverse_similitude B A μ hsim,
    ← mul_assoc, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero μ), one_mul]

@[expose] def similitudeConjugation (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) : MulAut (isometryGroup B) where
  toFun g := ⟨A * g.val * A⁻¹, similitude_conjugation_preserves B A μ hsim g⟩
  invFun g := ⟨A⁻¹ * g.val * A, by
    simpa using similitude_conjugation_preserves B A.symm μ⁻¹
      (inverse_similitude B A μ hsim) g⟩
  left_inv g := by apply Subtype.ext; change A⁻¹ * (A * g.val * A⁻¹) * A = g.val; group
  right_inv g := by apply Subtype.ext; change A * (A⁻¹ * g.val * A) * A⁻¹ = g.val; group
  map_mul' g h := by
    apply Subtype.ext
    change A * (g.val * h.val) * A⁻¹ = (A * g.val * A⁻¹) * (A * h.val * A⁻¹)
    group

theorem similitudeConjugation_val (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) (g : isometryGroup B) :
    (similitudeConjugation B A μ hsim g).val = A * g.val * A⁻¹ := rfl

theorem similitudeConjugation_apply (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) (g : isometryGroup B) (x : V) :
    (similitudeConjugation B A μ hsim g).val x = A (g.val (A.symm x)) := rfl

theorem fixed_similitudeConjugation_eq (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) :
    FixedCommutingProduct.fixedSubgroup (similitudeConjugation B A μ hsim) =
      symplecticOperatorCentralizer B A.toLinearMap := by
  ext g
  change similitudeConjugation B A μ hsim g = g ↔ ∀ x, g.val (A x) = A (g.val x)
  constructor
  · intro hg x
    have h := congrArg (fun z : isometryGroup B => z.val (A x)) hg
    change A (g.val (A.symm (A x))) = g.val (A x) at h
    rw [A.symm_apply_apply] at h
    exact h.symm
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change A (g.val (A.symm x)) = g.val x
    rw [← hg, A.apply_symm_apply]

@[expose] def fixedCentralizerEquiv (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) :
    FixedCommutingProduct.fixedSubgroup (similitudeConjugation B A μ hsim) ≃*
      symplecticOperatorCentralizer B A.toLinearMap :=
  MulEquiv.subgroupCongr (fixed_similitudeConjugation_eq B A μ hsim)

theorem similitudeConjugation_negIsometry (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) :
    similitudeConjugation B A μ hsim (negIsometry B) = negIsometry B := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change A (-(A.symm x)) = -x
  rw [map_neg, A.apply_symm_apply]

theorem scalarSigns_invariant (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) :
    (scalarSigns B).map (similitudeConjugation B A μ hsim).toMonoidHom = scalarSigns B :=
  scalarSigns_map_eq B _ (similitudeConjugation_negIsometry B A μ hsim)

@[expose] def projectiveConjugation (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) : MulAut (projectiveSymplectic B) :=
  CatalogueBFixedCentralQuotient.onQuotient (scalarSigns B) (similitudeConjugation B A μ hsim)
    (scalarSigns_invariant B A μ hsim)

theorem projectiveConjugation_mk (B : BilinForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) (g : isometryGroup B) :
    projectiveConjugation B A μ hsim (QuotientGroup.mk' (scalarSigns B) g) =
      QuotientGroup.mk' (scalarSigns B) (similitudeConjugation B A μ hsim g) :=
  CatalogueBFixedCentralQuotient.onQuotient_mk _ _ _ g

end CFSG.ComponentClassification.CatalogueBSymplecticB
