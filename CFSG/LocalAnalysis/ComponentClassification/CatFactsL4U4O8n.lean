module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8m
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8k
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8l
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUj

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {K : Type} [Field K] [Finite K] {b c : K}

omit [Finite K] in
theorem eq_scalar_of_mulVec {X : GL (Fin (2 * 4)) K} (u : Kˣ)
    (h : ∀ v, X.val *ᵥ v = (u : K) • v) : X = GeneralLinearGroup.scalar (Fin (2 * 4)) u := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  simp

omit [Finite K] in
theorem eq_scalar_mul_of_mulVec {X Y : GL (Fin (2 * 4)) K} (u : Kˣ)
    (h : ∀ v, X.val *ᵥ v = (u : K) • (Y.val *ᵥ v)) :
    X = GeneralLinearGroup.scalar (Fin (2 * 4)) u * Y := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, Units.val_mul, ← Matrix.mulVec_mulVec,
    GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  simp

omit [Finite K] in
theorem ne_zero_of_mulVec {X : GL (Fin (2 * 4)) K} {a : K} {f : (Fin (2 * 4) → K) → _}
    (h : ∀ v, X.val *ᵥ v = a • f v) : a ≠ 0 := by
  rintro rfl
  have h1 : X.val *ᵥ (Pi.single 0 1) = 0 := by rw [h, zero_smul]
  have h2 : X⁻¹.val *ᵥ (X.val *ᵥ Pi.single 0 1) = Pi.single 0 1 := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [h1, Matrix.mulVec_zero] at h2
  have := congrFun h2 0
  simp at this

theorem outer_cent_O8 {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hQ0 : ∃ v, Q8 K b c v ≠ 0) (φ : MulAut (G0 K b c))
    (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ c₀ : Kˣ)
    (hsim : ∀ x, Q8 K b c (A x) = (μ : K) * Q8 K b c x) (hsq : ∀ x, A (A x) = (c₀ : K) • x)
    (hμc : (μ : K) = c₀)
    (hns : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K (Fin (2 * 4) → K)))
    (gφ : similarityPairs (Q8 K b c))
    (hgφ : matrixProjectiveConjugationHom (Q8 K b c) gφ = MulAut.congr (psiC K b c) φ)
    (hgφ1 : gφ.val.right = 1) (hAg : A = matrixLinearEquiv gφ.val.left)
    [Fact (¬ IsSquare (c₀ : K))] (δ : (extension (c₀ : K))ˣ)
    (h2 : (2 : extension (c₀ : K)) ≠ 0)
    (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension (c₀ : K)))
    (y : SpecialLinearGroup (Fin 2) (extension (δ : extension (c₀ : K))) →*
      orthogonalDerived (Q8 K b c))
    (hχA : ∀ v, χ (A v) = (QuadraticAlgebra.omega : extension (c₀ : K)) • χ v)
    (hy : ∀ h v, (y h).val.val v =
      χ.symm ((OIU.Umat δ h2 h : Matrix (Fin 4) (Fin 4) (extension (c₀ : K))) *ᵥ χ v))
    (J' : Subgroup (G0 K b c))
    (hJy : ∀ x, x ∈ J' ↔ ∃ h, QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) (y h) =
        theta K b c hQ0 x)
    (ψ : MulAut (G0 K b c)) (hcomm : ψ * φ = φ * ψ) (hψJ : ∀ x ∈ J', ψ x = x) :
    ψ ∈ zpowers φ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hK
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have h2K : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hstated := stated K b c hp he hK hirr
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := CatalogueBOrthogonalPointData.coordinate_model_witness_minus
    hstated K hK b c hirr (MulEquiv.refl _)
  have hker := RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff
    (Q8 K b c) hnd hT hAP
  obtain ⟨g, hg⟩ := exists_pair K b c hp he hK hirr ψ
  have hfix : ∀ h, ψ ((theta K b c hQ0).symm (QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) (y h))) =
      (theta K b c hQ0).symm (QuotientGroup.mk' _ (y h)) := fun h =>
    hψJ _ ((hJy _).mpr ⟨h, (MulEquiv.apply_symm_apply _ _).symm⟩)
  have hg1 := right_eq_one hp hp2 he hK hQ0 ψ g hg (c₀ : K) δ h2 χ y hy hfix
  obtain ⟨l, hl⟩ := left_comm hnd hT hAP ψ φ g gφ hg hgφ hg1 hgφ1 hcomm
  have hAv : ∀ v, A v = gφ.val.left.val *ᵥ v := fun v => by rw [hAg]; rfl
  have hsq' : ∀ x, matrixLinearEquiv gφ.val.left (matrixLinearEquiv gφ.val.left x) =
      (c₀ : K) • x := fun x => by rw [← hAg]; exact hsq x
  have hl2 := sq_eq_one g.val.left gφ.val.left l c₀ (left_sq gφ c₀ hsq') hl
  have hχY : ∀ v, χ (gφ.val.left.val *ᵥ v) =
      (QuadraticAlgebra.omega : extension (c₀ : K)) • χ v := fun v => by
    rw [← hAv]; exact hχA v
  have hlpm : (l : K) = 1 ∨ (l : K) = -1 := by
    have := congrArg Units.val hl2
    rw [Units.val_mul, Units.val_one] at this
    exact mul_self_eq_one_iff.mp this
  rcases hlpm with hl1 | hl1
  swap
  · exfalso
    have hl' : l = -1 := Units.ext (by rw [hl1, Units.val_neg, Units.val_one])
    rw [hl'] at hl
    exact not_anticomm hp hp2 he hK hQ0 ψ g hg hg1 gφ.val.left (c₀ : K) δ h2 χ hχY y hy hfix hl
  have hl' : l = 1 := Units.ext (by rw [hl1, Units.val_one])
  rw [hl', map_one, one_mul] at hl
  have hcommU : ∀ U : Matrix (Fin 4) (Fin 4) (extension (c₀ : K)),
      U = OIL.mU1 ∨ U = OIL.mUw (δ : extension (c₀ : K)) ∨ U = OIL.mL1 →
        ∀ v, g.val.left.val *ᵥ χ.symm (U *ᵥ χ v) = χ.symm (U *ᵥ χ (g.val.left.val *ᵥ v)) := by
    have : CharP (extension (c₀ : K)) p :=
      charP_of_injective_algebraMap (algebraMap K _).injective p
    have key : ∀ u : SpecialLinearGroup (Fin 2) (extension (δ : extension (c₀ : K))), u ^ p = 1 →
        ∀ v, g.val.left.val *ᵥ χ.symm ((OIU.Umat δ h2 u : Matrix (Fin 4) (Fin 4) _) *ᵥ χ v) =
          χ.symm ((OIU.Umat δ h2 u : Matrix (Fin 4) (Fin 4) _) *ᵥ χ (g.val.left.val *ᵥ v)) := by
      intro u hu v
      have hW := congrArg Subtype.val
        (conj_eq_of_pow hQ0 ψ g hg (y u) (by rw [← map_pow, hu, map_one]) (hfix u))
      rw [matrixDerivedConjugation_val, hg1, map_one, MulAut.one_apply] at hW
      set W := ((derivedEquiv (Q8 K b c)).symm (y u)).val with hWdef
      have hWv : ∀ v, W.val *ᵥ v = (y u).val.val v := fun v => by
        rw [hWdef, ← Matrix.toLin'_apply, toLin'_derived]
        rfl
      have hXW : g.val.left * W = W * g.val.left := by
        calc g.val.left * W = g.val.left * W * g.val.left⁻¹ * g.val.left := by group
          _ = W * g.val.left := by rw [hW]
      rw [← hy, ← hWv, Matrix.mulVec_mulVec, ← Units.val_mul, hXW, Units.val_mul,
        ← Matrix.mulVec_mulVec, hWv, hy]
    rintro U (rfl | rfl | rfl) v
    · rw [← OIU.Umat_uE_one δ h2]
      exact key _ (OIL.uE_pow_char _ _) v
    · rw [← OIU.Umat_uE_omega δ h2]
      exact key _ (OIL.uE_pow_char _ _) v
    · rw [← OIU.Umat_lE_one δ h2]
      exact key _ (OIL.lE_pow_char _ _) v
  obtain ⟨m, hm⟩ := exists_scalar_E (c₀ : K) δ h2 χ g.val.left gφ.val.left hχY hl hcommU
  have hdec := eq_re_add_im (c₀ : K) χ g.val.left gφ.val.left hχY m hm
  have hc₀ : (c₀ : K) ≠ 0 := Units.ne_zero c₀
  have hμd : (μ : K) / (c₀ : K) = 1 := by rw [hμc]; exact div_self hc₀
  have hadj := positive_square_adjoint (Q8 K b c) A (c₀ : K) (μ : K) hc₀ hsq
    (polar_similarity (Q8 K b c) A μ hsim) hμd
  have hsimB : ∀ v, Q8 K b c (m.re • v + m.im • A.toLinearMap v) =
      (multiplier (Q8 K b c) g : K) * Q8 K b c v := fun v => by
    rw [LinearEquiv.coe_toLinearMap, hAv, ← hdec]
    exact matrix_similarity (Q8 K b c) g hg1 v
  have hz := re_im_eq_zero (Q8 K b c) hnd h2K A.toLinearMap (c₀ : K)
    (fun v => by rw [LinearEquiv.coe_toLinearMap, hsim, hμc])
    (fun x y => hadj x y) (fun k hk => hns k (by rw [hk]; rfl)) m.re m.im _ hsimB
  rcases hz with hre | him
  ·
    have hm0 : m.im ≠ 0 := ne_zero_of_mulVec (f := fun v => gφ.val.left.val *ᵥ v)
      (fun v => by rw [hdec, hre, zero_smul, zero_add])
    have hX := eq_scalar_mul_of_mulVec (X := g.val.left) (Y := gφ.val.left) (Units.mk0 _ hm0)
      (fun v => by rw [hdec, hre, zero_smul, zero_add, Units.val_mk0])
    have h1 : matrixProjectiveConjugationHom (Q8 K b c) (g * gφ⁻¹) = 1 := by
      refine (hker _).mpr ⟨?_, Units.mk0 _ hm0, ?_⟩
      · change (g.val * gφ.val⁻¹).right = 1
        rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hg1, hgφ1, inv_one,
          mul_one]
      · change (g.val * gφ.val⁻¹).left = _
        rw [SemidirectProduct.mul_left, SemidirectProduct.inv_left, hg1, hgφ1, inv_one, map_one]
        simp only [MulAut.one_apply]
        rw [hX, mul_assoc, mul_inv_cancel, mul_one]
    rw [map_mul, map_inv, hg, hgφ, mul_inv_eq_one] at h1
    rw [(MulAut.congr (psiC K b c)).injective h1]
    exact mem_zpowers φ
  ·
    have hm0 : m.re ≠ 0 := ne_zero_of_mulVec (f := id)
      (fun v => by rw [hdec, him, zero_smul, add_zero]; rfl)
    have hX := eq_scalar_of_mulVec (X := g.val.left) (Units.mk0 _ hm0)
      (fun v => by rw [hdec, him, zero_smul, add_zero, Units.val_mk0])
    have h1 := (hker g).mpr ⟨hg1, Units.mk0 _ hm0, hX⟩
    rw [hg, ← map_one (MulAut.congr (psiC K b c))] at h1
    rw [(MulAut.congr (psiC K b c)).injective h1]
    exact one_mem _

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
