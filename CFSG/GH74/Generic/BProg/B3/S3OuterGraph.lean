module

public import CFSG.GH74.Generic.BProg.B3.S3OuterCore
public import CFSG.GH74.Generic.BProg.B3.S3OuterRank
public import CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3
public import CFSG.GH74.Generic.BProg.B3.L2CompL3b

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3OuterGraph

open CFSG CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix Polynomial Subgroup S3OuterCore
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

theorem poly_id_aeval (C : Matrix (Fin 3) (Fin 3) F) (hc4 : C * C * (C * C) = 1) (p q r : F)
    (h1 : p ^ 2 + r ^ 2 + 2 * q ^ 2 = 0) (h2 : 2 * p * r - 2 * q ^ 2 = 1) :
    aeval C (Polynomial.C p + Polynomial.C q * X + Polynomial.C r * X ^ 2 -
        Polynomial.C q * X ^ 3 : F[X]) *
      aeval C (Polynomial.C p - Polynomial.C q * X + Polynomial.C r * X ^ 2 +
        Polynomial.C q * X ^ 3 : F[X]) = C * C := by
  have key : (Polynomial.C p + Polynomial.C q * X + Polynomial.C r * X ^ 2 -
      Polynomial.C q * X ^ 3 : F[X]) *
      (Polynomial.C p - Polynomial.C q * X + Polynomial.C r * X ^ 2 + Polynomial.C q * X ^ 3 : F[X])
      = X ^ 2 + (X ^ 4 - 1) *
        (Polynomial.C (r ^ 2 + 2 * q ^ 2) - Polynomial.C (q ^ 2) * X ^ 2) := by
    have e0 : Polynomial.C (p ^ 2 + r ^ 2 + 2 * q ^ 2) = (0 : F[X]) := by rw [h1]; simp
    have e1 : Polynomial.C (2 * p * r - 2 * q ^ 2) = (1 : F[X]) := by rw [h2]; simp
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at e0 e1 ⊢
    linear_combination e0 + X ^ 2 * e1
  rw [← map_mul, key]
  have h4 : C ^ 4 = 1 := by rw [show C ^ 4 = C * C * (C * C) by noncomm_ring]; exact hc4
  simp [h4, pow_two]

theorem poly_id (C : Matrix (Fin 3) (Fin 3) F) (hc4 : C * C * (C * C) = 1) (p q r : F)
    (h1 : p ^ 2 + r ^ 2 + 2 * q ^ 2 = 0) (h2 : 2 * p * r - 2 * q ^ 2 = 1) :
    (p • (1 : Matrix (Fin 3) (Fin 3) F) + q • C + r • (C * C) - q • (C * C * C)) *
      (p • (1 : Matrix (Fin 3) (Fin 3) F) - q • C + r • (C * C) + q • (C * C * C)) = C * C := by
  have := poly_id_aeval C hc4 p q r h1 h2
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul] at this
  convert this using 2 <;> simp [pow_succ, mul_assoc]

theorem B_rel (B C : Matrix (Fin 3) (Fin 3) F) (hcB : C * B * Cᵀ = B) (hc4 : C * C * (C * C) = 1)
    (p q r : F) :
    B * (p • (1 : Matrix (Fin 3) (Fin 3) F) + q • C + r • (C * C) - q • (C * C * C))ᵀ =
      (p • (1 : Matrix (Fin 3) (Fin 3) F) - q • C + r • (C * C) + q • (C * C * C)) * B := by
  have hCi : C * C * C * C = 1 := by
    have : C * C * C * C = C * C * (C * C) := by noncomm_ring
    rw [this, hc4]
  have R1 : B * Cᵀ = (C * C * C) * B := by
    calc B * Cᵀ = (C * C * C * C) * B * Cᵀ := by rw [hCi, one_mul]
      _ = (C * C * C) * (C * B * Cᵀ) := by noncomm_ring
      _ = (C * C * C) * B := by rw [hcB]
  have R2 : B * (Cᵀ * Cᵀ) = (C * C) * B := by
    calc B * (Cᵀ * Cᵀ) = (B * Cᵀ) * Cᵀ := (Matrix.mul_assoc _ _ _).symm
      _ = ((C * C * C) * B) * Cᵀ := by rw [R1]
      _ = (C * C * C) * (B * Cᵀ) := Matrix.mul_assoc _ _ _
      _ = (C * C * C) * ((C * C * C) * B) := by rw [R1]
      _ = ((C * C * C) * (C * C * C)) * B := (Matrix.mul_assoc _ _ _).symm
      _ = ((C * C) * (C * C * C * C)) * B := by noncomm_ring
      _ = (C * C) * B := by rw [hCi, mul_one]
  have R3 : B * (Cᵀ * (Cᵀ * Cᵀ)) = C * B := by
    calc B * (Cᵀ * (Cᵀ * Cᵀ)) = (B * (Cᵀ * Cᵀ)) * Cᵀ := by noncomm_ring
      _ = ((C * C) * B) * Cᵀ := by rw [R2]
      _ = (C * C) * (B * Cᵀ) := Matrix.mul_assoc _ _ _
      _ = (C * C) * ((C * C * C) * B) := by rw [R1]
      _ = (C * (C * C * C * C)) * B := by noncomm_ring
      _ = C * B := by rw [hCi, mul_one]
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_one, R1, R2, R3,
    Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  abel

theorem twist_exists (h2 : (2 : F) ≠ 0) (B C : Matrix (Fin 3) (Fin 3) F) (hcB : C * B * Cᵀ = B)
    (hc4 : C * C * (C * C) = 1) (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    ∃ K : Matrix (Fin 3) (Fin 3) F, K * B * Kᵀ = (C * C) * B := by
  have h1 : ((1 + a) / 2) ^ 2 + ((1 - a) / 2) ^ 2 + 2 * (b / 2) ^ 2 = 0 := by
    field_simp
    linear_combination 2 * hab
  have h2' : 2 * ((1 + a) / 2) * ((1 - a) / 2) - 2 * (b / 2) ^ 2 = 1 := by
    field_simp
    linear_combination (-1) * hab
  refine ⟨((1 + a) / 2) • (1 : Matrix (Fin 3) (Fin 3) F) + (b / 2) • C + ((1 - a) / 2) • (C * C) -
    (b / 2) • (C * C * C), ?_⟩
  rw [Matrix.mul_assoc, B_rel B C hcB hc4, ← Matrix.mul_assoc, poly_id C hc4 _ _ _ h1 h2']

theorem exists_sl_twist (B : GL (Fin 3) F) (T : SL(3, F)) (hTT : T * T = 1)
    (K : Matrix (Fin 3) (Fin 3) F)
    (hK : K * (B : Matrix (Fin 3) (Fin 3) F) * Kᵀ = (T : Matrix (Fin 3) (Fin 3) F) *
      (B : Matrix (Fin 3) (Fin 3) F)) :
    ∃ k : SL(3, F), (CatalogueBHigherLinearAction.slConjugation 3 F B *
      CatalogueBGraphForm.slGraphAut 3 F) k = T * k := by
  have hBdet : (B : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  have hTdet : (T : Matrix (Fin 3) (Fin 3) F).det = 1 := T.2
  have hTT' : (T : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) hTT
    simpa using this
  have hsq : K.det * K.det = 1 := by
    have h := congrArg Matrix.det hK
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul, hTdet, one_mul] at h
    exact mul_right_cancel₀ hBdet (by rw [one_mul]; linear_combination h)
  set ε : F := K.det with hεdef
  have hε2 : ε * ε = 1 := hsq
  set K' : Matrix (Fin 3) (Fin 3) F := ε • K with hK'
  have hdet' : K'.det = 1 := by
    rw [hK', Matrix.det_smul, Fintype.card_fin, ← hεdef]
    calc ε ^ 3 * ε = (ε * ε) * (ε * ε) := by ring
      _ = 1 := by rw [hε2, one_mul]
  have hK'B : K' * (B : Matrix (Fin 3) (Fin 3) F) * K'ᵀ =
      (T : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) := by
    rw [hK', Matrix.transpose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε2, one_smul]
    exact hK
  obtain ⟨kS, hkS⟩ : ∃ kS : SL(3, F), (kS : Matrix (Fin 3) (Fin 3) F) = K' := ⟨⟨K', hdet'⟩, rfl⟩
  refine ⟨kS, ?_⟩
  apply Subtype.ext
  change ((CatalogueBHigherLinearAction.slConjugation 3 F B
      (CatalogueBGraphForm.slGraphAut 3 F kS) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    ((T * kS : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
  rw [Matrix.SpecialLinearGroup.coe_mul, CatalogueBHigherLinearAction.slConjugation_matrix,
    CatalogueBGraphForm.slGraphAut_matrix]
  set M : Matrix (Fin 3) (Fin 3) F := ((kS⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) with hM
  have hMK : M * K' = 1 := by
    rw [← hkS, hM, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hMKt : K'ᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hMK, Matrix.transpose_one]
  have hBM : (B : Matrix (Fin 3) (Fin 3) F) * Mᵀ =
      (T : Matrix (Fin 3) (Fin 3) F) * K' * (B : Matrix (Fin 3) (Fin 3) F) := by
    calc (B : Matrix (Fin 3) (Fin 3) F) * Mᵀ
        = ((T : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F)) *
            ((B : Matrix (Fin 3) (Fin 3) F) * Mᵀ) := by rw [hTT', one_mul]
      _ = (T : Matrix (Fin 3) (Fin 3) F) * ((T : Matrix (Fin 3) (Fin 3) F) *
            (B : Matrix (Fin 3) (Fin 3) F)) * Mᵀ := by noncomm_ring
      _ = (T : Matrix (Fin 3) (Fin 3) F) * (K' * (B : Matrix (Fin 3) (Fin 3) F) * K'ᵀ) * Mᵀ := by
          rw [hK'B]
      _ = (T : Matrix (Fin 3) (Fin 3) F) * (K' * (B : Matrix (Fin 3) (Fin 3) F)) * (K'ᵀ * Mᵀ) := by
          noncomm_ring
      _ = (T : Matrix (Fin 3) (Fin 3) F) * K' * (B : Matrix (Fin 3) (Fin 3) F) := by
          rw [hMKt, Matrix.mul_one]; noncomm_ring
  rw [hkS]
  calc (B : Matrix (Fin 3) (Fin 3) F) * Mᵀ * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = (T : Matrix (Fin 3) (Fin 3) F) * K' * ((B : Matrix (Fin 3) (Fin 3) F) *
          ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
        rw [hBM]; noncomm_ring
    _ = (T : Matrix (Fin 3) (Fin 3) F) * K' := by rw [Units.mul_inv, Matrix.mul_one]

theorem exists_sq_add_sq_neg_one [Finite F] : ∃ a b : F, a ^ 2 + b ^ 2 = -1 := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have : NeZero p := ⟨CharP.char_ne_zero_of_finite F p⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F p (-1)
  exact ⟨a, b, by simpa using hab⟩

theorem outerCore_graph [Finite F] (hF : ringChar F ≠ 2) (h5 : 5 ≤ Nat.card F) (B : GL (Fin 3) F)
    (hB : (B : Matrix (Fin 3) (Fin 3) F)ᵀ = B) : OuterCore (conjAut 3 F B * dualAut 3 F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hBdet : IsUnit (B : Matrix (Fin 3) (Fin 3) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  have hk2 : Nat.card F ≠ 2 := by omega
  have h3 : Nat.card F ≠ 3 := by omega
  obtain ⟨N, hNq, hNfix, hNnorm, hNcomm, ⟨eN⟩⟩ :=
    B2.PumpupTableOutL3.lin_graph_centralizer_psl2 hF h3 hB
  obtain ⟨cm, bm, hcdet, hcB, hnsc, hc4, hbdet, hbB, hb2, hbc⟩ :=
    L2CompSymD8.exists_isometry_D8 h2 (le_refl 3) (B : Matrix (Fin 3) (Fin 3) F) hB hBdet
  obtain ⟨c, hcm⟩ : ∃ c : SL(3, F), (c : Matrix (Fin 3) (Fin 3) F) = cm := ⟨⟨cm, hcdet⟩, rfl⟩
  obtain ⟨b, hbm⟩ : ∃ b : SL(3, F), (b : Matrix (Fin 3) (Fin 3) F) = bm := ⟨⟨bm, hbdet⟩, rfl⟩
  have hc4' : (c * c) * (c * c) = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hcm]
    exact hc4
  have hb2' : b * b = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hbm]
    exact hb2
  have hbc' : b * c * b⁻¹ = c⁻¹ := by
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2'
    have h4 : b * c * b = c * c * c := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul, hcm, hbm]
      exact hbc
    have hci : c⁻¹ = c * c * c := inv_eq_of_mul_eq_one_right (by
      have : c * (c * c * c) = (c * c) * (c * c) := by group
      rw [this]
      exact hc4')
    rw [hbi, h4, hci]
  have hfix : ∀ x : SL(3, F), (x : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) *
      (x : Matrix (Fin 3) (Fin 3) F)ᵀ = B →
        (conjAut 3 F B * dualAut 3 F) (LinearFlag.proj 3 F x) = LinearFlag.proj 3 F x := by
    intro x hx
    rw [← CFSG.GH74.Generic.S45.proj_slConjugation_slGraphAut,
      L2CompL3b.fixed_of_isometry B hB x hx]
  have hbfix := hfix b (by rw [hbm]; exact hbB)
  have hcfix := hfix c (by rw [hcm]; exact hcB)
  have hcc : (c * c : SL(3, F)) = (c * c)⁻¹ := (inv_eq_of_mul_eq_one_right hc4').symm
  have hcomm : ⁅LinearFlag.proj 3 F b, LinearFlag.proj 3 F c⁆ = LinearFlag.proj 3 F (c * c) := by
    rw [← map_commutatorElement, commutatorElement_def, hbc', hcc, _root_.mul_inv_rev]
  obtain ⟨a, b', hab⟩ := exists_sq_add_sq_neg_one (F := F)
  obtain ⟨K, hK⟩ := twist_exists h2 (B : Matrix (Fin 3) (Fin 3) F) cm hcB hc4 a b' hab
  have hK' : K * (B : Matrix (Fin 3) (Fin 3) F) * Kᵀ =
      ((c * c : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hcm]
    exact hK
  obtain ⟨k, hk⟩ := exists_sl_twist B (c * c) hc4' K hK'
  refine ⟨N, hNq, S3OuterRank.two_le_pRank_of_psl2 hNq hk2 h3 eN, hNfix, hNnorm,
    LinearFlag.proj 3 F (c * c), ?_, ?_, ?_, LinearFlag.proj 3 F k, ?_⟩
  · rw [← hcomm]
    exact hNcomm _ _ hbfix hcfix
  · rw [← map_mul, hc4', map_one]
  · intro h
    obtain ⟨l, -, hl⟩ := LinearFlag.proj_eq_one_iff.1 h
    apply hnsc (l : F)
    have : ((c * c : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = cm * cm := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hcm]
    rw [← this, hl, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  · rw [← CFSG.GH74.Generic.S45.proj_slConjugation_slGraphAut, hk, map_mul, mul_inv_cancel_right]

end S3OuterGraph

end CFSG.GH74.Generic.BProg.B3
