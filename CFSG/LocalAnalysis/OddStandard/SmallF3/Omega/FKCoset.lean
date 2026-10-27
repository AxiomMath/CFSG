module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKDiagDef
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import CFSG.LieType.Universal.SpinOmega.Range

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution
open QuadraticMap
open CliffordAlgebra

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

private noncomputable instance fkInvertibleTwo : Invertible (2 : 𝔽₃) :=
  invertibleOfNonzero (by
    have h3 : (3 : 𝔽₃) = 0 := CharP.cast_eq_zero (R := 𝔽₃) (p := 3)
    have hsum : (2 : 𝔽₃) + 1 = 0 := by
      have : (2 : 𝔽₃) + 1 = (3 : 𝔽₃) := by norm_num
      rw [this, h3]
    have h2eq : (2 : 𝔽₃) = -1 := eq_neg_of_add_eq_zero_left hsum
    rw [h2eq]
    exact neg_ne_zero.mpr one_ne_zero)

private lemma fk_unit_sq_one (u : 𝔽₃ˣ) : u * u = 1 := by
  haveI : Fintype 𝔽₃ := Fintype.ofFinite _
  have hcard : Fintype.card 𝔽₃ = 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 one_ne_zero, pow_one]
  have h := FiniteField.pow_card (u : 𝔽₃)
  rw [hcard] at h
  have hd : (u : 𝔽₃) ≠ 0 := u.ne_zero
  have : (u : 𝔽₃) * ((u : 𝔽₃) ^ 2 - 1) = 0 := by linear_combination h
  have hu2 : (u : 𝔽₃) ^ 2 = 1 := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hd)
  exact Units.ext (by simpa [pow_two] using hu2)

private lemma fk_units_f3 (u : 𝔽₃ˣ) : u = 1 ∨ u = -1 := by
  have hsq : (u : 𝔽₃) * (u : 𝔽₃) = 1 := by
    have := congrArg (fun v : 𝔽₃ˣ => (v : 𝔽₃)) (fk_unit_sq_one u)
    simpa using this
  have h : ((u : 𝔽₃) - 1) * ((u : 𝔽₃) + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp h with h | h
  · left; exact Units.ext (sub_eq_zero.mp h)
  · right; exact Units.ext (eq_neg_of_add_eq_zero_left h)

private lemma fk_squareClass_f3 (x : TauCeti.SquareClassGroup 𝔽₃) :
    x = 0 ∨ x = TauCeti.squareClass (-1 : 𝔽₃ˣ) := by
  have h := fk_units_f3 (Additive.toMul (Quotient.out x))
  rw [← TauCeti.squareClass_toMul_out x]
  rcases h with h | h <;> rw [h]
  · left
    rw [TauCeti.squareClass_eq_zero_iff]
    exact ⟨1, by simp⟩
  · right
    rfl

private lemma fkDiag_det (d : Fin 4 ⊕ Fin 4 → 𝔽₃ˣ) :
    LinearEquiv.det (fkDiag d) = ∏ i, d i := by
  ext
  rw [LinearEquiv.coe_det]
  have hmat : (fkDiag d : (Fin 4 ⊕ Fin 4 → 𝔽₃) →ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) =
      Matrix.toLin' (Matrix.diagonal fun i => (d i : 𝔽₃)) := by
    apply LinearMap.ext
    intro v
    funext i
    rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    exact fkDiag_apply d v i
  rw [hmat, LinearMap.det_toLin', Matrix.det_diagonal]
  simp

private lemma fkD0_det_units : LinearEquiv.det (fkDiag fkD0) = 1 := by
  rw [fkDiag_det]
  apply Units.ext
  rw [Units.coe_prod, Units.val_one, Fintype.prod_sum_type]
  have h4 : ((-1 : 𝔽₃) ^ 4) = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    simp [pow_two, neg_mul_neg]
  simp [fkD0, h4, one_mul]

private noncomputable def fkV1 : Fin 4 ⊕ Fin 4 → 𝔽₃ :=
  Pi.single (Sum.inl 0) 1 - Pi.single (Sum.inr 0) 1

private noncomputable def fkV2 : Fin 4 ⊕ Fin 4 → 𝔽₃ :=
  Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1

private lemma fk_quad_v1 : Q₄ fkV1 = -1 := by
  have h := map_hypPair_add_smul (plusPair 𝔽₃ (0 : Fin 4)) (-1)
  simpa [fkV1, plusPair_e, plusPair_f, sub_eq_add_neg] using h

private lemma fk_quad_v2 : Q₄ fkV2 = 1 := by
  have h := map_hypPair_add_smul (plusPair 𝔽₃ (0 : Fin 4)) (1 : 𝔽₃)
  simpa [fkV2, plusPair_e, plusPair_f] using h

private lemma fk_polar_v1 (y : Fin 4 ⊕ Fin 4 → 𝔽₃) :
    polar Q₄ fkV1 y = y (Sum.inr 0) - y (Sum.inl 0) := by
  rw [fkV1, sub_eq_add_neg, polar_add_left, polar_neg_left]
  simp only [polar_single_inl_quadPlus, polar_single_inr_quadPlus]
  ring

private lemma fk_polar_v2 (y : Fin 4 ⊕ Fin 4 → 𝔽₃) :
    polar Q₄ fkV2 y = y (Sum.inl 0) + y (Sum.inr 0) := by
  rw [fkV2, polar_add_left]
  simp only [polar_single_inl_quadPlus, polar_single_inr_quadPlus]
  ring

private noncomputable instance fkInvertibleQV1 : Invertible (Q₄ fkV1) :=
  invertibleOfNonzero (by rw [fk_quad_v1]; exact neg_ne_zero.mpr one_ne_zero)

private noncomputable instance fkInvertibleQV2 : Invertible (Q₄ fkV2) :=
  invertibleOfNonzero (by rw [fk_quad_v2]; exact one_ne_zero)

private lemma fk_reflect_v1 (y : Fin 4 ⊕ Fin 4 → 𝔽₃) :
    TauCeti.QuadraticMap.reflection Q₄ fkV1 y =
      y + (y (Sum.inr 0) - y (Sum.inl 0)) • fkV1 := by
  rw [TauCeti.QuadraticMap.reflection_apply]
  have h : ⅟(Q₄ fkV1) = -1 := by
    apply invOf_eq_right_inv
    rw [fk_quad_v1]
    ring
  rw [h, fk_polar_v1]
  simp only [neg_mul, one_mul, neg_smul, sub_neg_eq_add]

private lemma fk_reflect_v2 (z : Fin 4 ⊕ Fin 4 → 𝔽₃) :
    TauCeti.QuadraticMap.reflection Q₄ fkV2 z =
      z - (z (Sum.inl 0) + z (Sum.inr 0)) • fkV2 := by
  rw [TauCeti.QuadraticMap.reflection_apply]
  have h : ⅟(Q₄ fkV2) = 1 := by
    apply invOf_eq_right_inv
    rw [fk_quad_v2]
    simp
  rw [h, fk_polar_v2]
  simp

private noncomputable def fkDK : Fin 4 ⊕ Fin 4 → 𝔽₃ˣ :=
  Sum.elim ![-1, 1, 1, 1] ![-1, 1, 1, 1]

private lemma fkDiag_dk_eq_reflection :
    fkDiag fkDK = TauCeti.QuadraticMap.reflection Q₄ fkV2 *
      TauCeti.QuadraticMap.reflection Q₄ fkV1 := by
  apply LinearEquiv.ext
  intro y
  funext i
  rw [LinearEquiv.mul_apply, fk_reflect_v1, fk_reflect_v2, fkDiag_apply]
  rcases i with m | m <;> fin_cases m <;>
    simp [fkV1, fkV2, fkDK, Pi.single_apply] <;> ring

private lemma fkDK_mul (m : Fin 4) : (fkDK (.inl m) : 𝔽₃) * fkDK (.inr m) = 1 := by
  fin_cases m <;> simp [fkDK]

private lemma fk_quad_fkDK (v : Fin 4 ⊕ Fin 4 → 𝔽₃) : Q₄ (fkDiag fkDK v) = Q₄ v := by
  have h := quadPlus_fkDiag fkDK 1 fkDK_mul v
  rwa [one_mul] at h

private lemma fk_quad_fkDK_mem : fkDiag fkDK ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  exact fk_quad_fkDK

private lemma fkDiag_mul (d e : Fin 4 ⊕ Fin 4 → 𝔽₃ˣ) :
    fkDiag d * fkDiag e = fkDiag (d * e) := by
  apply LinearEquiv.ext
  intro v
  funext i
  simp only [LinearEquiv.mul_apply, fkDiag_apply, Pi.mul_apply, Units.val_mul]
  ring

private lemma fkDiag_inv (d : Fin 4 ⊕ Fin 4 → 𝔽₃ˣ) :
    fkDiag d⁻¹ = (fkDiag d)⁻¹ := by
  apply LinearEquiv.ext
  intro v
  funext i
  simp only [fkDiag_apply, fkDiag_symm_apply, Pi.inv_apply]

private lemma fkD0_inv_mul_eq_dk : fkD0⁻¹ * fkD1 = fkDK := by
  funext i
  rcases i with m | m <;> fin_cases m <;> simp [fkDK, fkD0, fkD1]

private lemma fkDiag_dk_eq_inv_mul :
    fkDiag fkDK = (fkDiag fkD0)⁻¹ * fkDiag fkD1 := by
  rw [← fkDiag_inv, fkDiag_mul, fkD0_inv_mul_eq_dk]

private lemma fk_quad_fkD0_neg (w : Fin 4 ⊕ Fin 4 → 𝔽₃) : Q₄ (fkDiag fkD0 w) = -Q₄ w := by
  have h := quadPlus_fkDiag fkD0 (-1) fkD0_mul w
  rwa [neg_one_mul] at h

private noncomputable def fkKO : TauCeti.QuadraticMap.orthogonalGroup Q₄ :=
  ⟨fkDiag fkDK, fk_quad_fkDK_mem⟩

private lemma fkKO_eq : fkKO = TauCeti.QuadraticMap.reflectionOrthogonal Q₄ fkV2 *
    TauCeti.QuadraticMap.reflectionOrthogonal Q₄ fkV1 := by
  apply Subtype.ext
  simpa [fkKO, Subgroup.coe_mul] using fkDiag_dk_eq_reflection

private lemma fk_neg_one_units_mul : (-1 : 𝔽₃ˣ) * (-1) = 1 := by
  ext
  simp [Units.val_mul, Units.val_neg, Units.val_one, neg_mul_neg]

private lemma fk_detSpinorNorm_KO (hQ : (quadPlus 4 𝔽₃).Nondegenerate) :
    detSpinorNorm hQ fkKO = (1, TauCeti.squareClassHom (-1 : 𝔽₃ˣ)) := by
  rw [fkKO_eq, map_mul, detSpinorNorm_reflectionOrthogonal, detSpinorNorm_reflectionOrthogonal]
  have hu1 : unitOfInvertible (Q₄ fkV1) = (-1 : 𝔽₃ˣ) :=
    Units.ext (by simp [val_unitOfInvertible, fk_quad_v1])
  have hu2 : unitOfInvertible (Q₄ fkV2) = (1 : 𝔽₃ˣ) :=
    Units.ext (by simp [val_unitOfInvertible, fk_quad_v2])
  rw [hu1, hu2, map_one]
  ext <;> simp [fk_neg_one_units_mul]

theorem fk_coset
    (a : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1] (Fin 4 ⊕ Fin 4 → GaloisField 3 1))
    (hQ : ∀ v, quadPlus 4 (GaloisField 3 1) (a v) = -quadPlus 4 (GaloisField 3 1) v)
    (hdet : LinearMap.det (a : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) →ₗ[GaloisField 3 1]
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1)) = 1) :
    ∃ (d : Fin 4 ⊕ Fin 4 → (GaloisField 3 1)ˣ) (y : spinGroup (quadPlus 4 (GaloisField 3 1))),
      (d = fkD0 ∨ d = fkD1) ∧ a = fkDiag d * spinAction (quadPlus 4 (GaloisField 3 1)) y := by
  classical
  have hpolar : (polarBilin Q₄).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 𝔽₃
  have hQnd : (quadPlus 4 𝔽₃).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hpolar
  have h12 : (plusPair 𝔽₃ (0 : Fin 4)).Orth (plusPair 𝔽₃ (1 : Fin 4)) :=
    plusPair_orth (by decide)
  have h13 : (plusPair 𝔽₃ (0 : Fin 4)).Orth (plusPair 𝔽₃ (2 : Fin 4)) :=
    plusPair_orth (by decide)
  have h23 : (plusPair 𝔽₃ (1 : Fin 4)).Orth (plusPair 𝔽₃ (2 : Fin 4)) :=
    plusPair_orth (by decide)
  have hidx := orthogonalGroup_index_four hpolar h12 h13 h23
  let c : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃) := (fkDiag fkD0)⁻¹ * a
  have hc_mem : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    have h1 : Q₄ (a v) = -Q₄ ((fkDiag fkD0)⁻¹ (a v)) := by
      have h := fk_quad_fkD0_neg ((fkDiag fkD0)⁻¹ (a v))
      simpa using h
    have h2 := hQ v
    have h3 : -Q₄ ((fkDiag fkD0)⁻¹ (a v)) = -Q₄ v := by rw [← h1, h2]
    exact neg_injective h3
  let cO : TauCeti.QuadraticMap.orthogonalGroup Q₄ := ⟨c, hc_mem⟩
  have hdet_aU : LinearEquiv.det a = 1 :=
    Units.ext (by rw [LinearEquiv.coe_det, hdet, Units.val_one])
  have hdet_cU : LinearEquiv.det c = 1 := by
    have hc_eq : c = (fkDiag fkD0)⁻¹ * a := rfl
    rw [hc_eq, map_mul, map_inv, fkD0_det_units, hdet_aU]
    simp
  set θ : Multiplicative (TauCeti.SquareClassGroup 𝔽₃) := orthogonalSpinorNorm Q₄ hQnd cO
    with hθdef
  have hdc : detSpinorNorm hQnd cO = (1, θ) := by
    rw [detSpinorNorm_apply, hθdef, QuadraticMap.orthogonalDet_apply, hdet_cU]
  by_cases hc1 : detSpinorNorm hQnd cO = 1
  · have hmem : (cO : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) ∈
        elementaryGroup Q₄ := (hidx.2 cO).mpr hc1
    have hmem' : c ∈ (spinAction Q₄).range := by
      rwa [← range_spinAction_quadPlus (K := 𝔽₃) (n := 4) (by norm_num : 3 ≤ 4)] at hmem
    obtain ⟨y, hy⟩ := hmem'
    refine ⟨fkD0, y, Or.inl rfl, ?_⟩
    rw [hy]
    show a = fkDiag fkD0 * c
    rw [show c = (fkDiag fkD0)⁻¹ * a from rfl]
    group
  · have hθ' : θ = 1 ∨ θ = TauCeti.squareClassHom (-1 : 𝔽₃ˣ) := by
      rcases fk_squareClass_f3 (Multiplicative.toAdd θ) with h | h
      · left
        rw [← ofAdd_toAdd θ, h, ofAdd_zero]
      · right
        rw [← ofAdd_toAdd θ, h, TauCeti.squareClassHom_apply]
    have hdet_kc : detSpinorNorm hQnd (fkKO⁻¹ * cO) = 1 := by
      rw [map_mul, map_inv, fk_detSpinorNorm_KO hQnd, hdc]
      rcases hθ' with h1 | h2
      · exact absurd (by rw [hdc, h1]; rfl) hc1
      · rw [h2]
        ext <;> simp
    have hk_mem : (fkKO⁻¹ * cO : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) ∈
        elementaryGroup Q₄ := (hidx.2 (fkKO⁻¹ * cO)).mpr hdet_kc
    have hk_mem' : (fkKO⁻¹ * cO : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) ∈
        (spinAction Q₄).range := by
      rwa [← range_spinAction_quadPlus (K := 𝔽₃) (n := 4) (by norm_num : 3 ≤ 4)] at hk_mem
    obtain ⟨y, hy⟩ := hk_mem'
    refine ⟨fkD1, y, Or.inr rfl, ?_⟩
    rw [hy]
    have hkc : ((↑(fkKO⁻¹) : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃]
          (Fin 4 ⊕ Fin 4 → 𝔽₃)) *
          (↑cO : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃))) =
        (fkDiag fkDK)⁻¹ * c := by
      simp [fkKO, cO]
    rw [hkc, show c = (fkDiag fkD0)⁻¹ * a from rfl, fkDiag_dk_eq_inv_mul]
    group

end CFSG.OddStandard.SmallF3.Omega
