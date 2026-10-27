module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLe

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace IdxSp

open Matrix CFSG.ComponentClassification.CatFactsL4U4.DiagL

variable {F : Type} [Field F]

@[expose] noncomputable def conjInv (P : Matrix (Fin 4) (Fin 4) F) (hP : IsUnit P.det) :
    SpecialLinearGroup (Fin 4) F →* SpecialLinearGroup (Fin 4) F where
  toFun y := ⟨P⁻¹ * y * P, by
    rw [det_mul, det_mul, y.2, mul_one, ← det_mul, nonsing_inv_mul P hP, det_one]⟩
  map_one' := by
    apply Subtype.ext
    change P⁻¹ * 1 * P = 1
    rw [Matrix.mul_one, nonsing_inv_mul P hP]
  map_mul' x y := by
    apply Subtype.ext
    change P⁻¹ * ((x : Matrix (Fin 4) (Fin 4) F) * y) * P = P⁻¹ * x * P * (P⁻¹ * y * P)
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left P _ hP]

theorem coe_conjInv (P : Matrix (Fin 4) (Fin 4) F) (hP : IsUnit P.det)
    (y : SpecialLinearGroup (Fin 4) F) :
    ((conjInv P hP y : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      P⁻¹ * y * P := rfl

theorem conjInv_injective (P : Matrix (Fin 4) (Fin 4) F) (hP : IsUnit P.det) :
    Function.Injective (conjInv P hP) := by
  intro x y hxy
  have h := congrArg (fun z : SpecialLinearGroup (Fin 4) F =>
    P * ((z : Matrix (Fin 4) (Fin 4) F) * P⁻¹)) hxy
  simp only [coe_conjInv, Matrix.mul_assoc, mul_nonsing_inv P hP, Matrix.mul_one,
    mul_nonsing_inv_cancel_left P _ hP] at h
  exact Subtype.ext h

theorem inv_mul_eq {d : F} {A P : Matrix (Fin 4) (Fin 4) F} (hP : IsUnit P.det)
    (hAP : A * P = P * kZero d) : P⁻¹ * A = kZero d * P⁻¹ := by
  calc P⁻¹ * A = P⁻¹ * (A * P) * P⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv P hP, Matrix.mul_one]
    _ = P⁻¹ * (P * kZero d) * P⁻¹ := by rw [hAP]
    _ = kZero d * P⁻¹ := by rw [nonsing_inv_mul_cancel_left P _ hP]

theorem mem_of_card [Fintype F] {d : F} (hns : ¬ IsSquare d) {A : Matrix (Fin 4) (Fin 4) F}
    {P : Matrix (Fin 4) (Fin 4) F} (hP : IsUnit P.det) (hAP : A * P = P * kZero d)
    {Y : Subgroup (SpecialLinearGroup (Fin 4) F)}
    (hYA : ∀ y ∈ Y, (y : Matrix (Fin 4) (Fin 4) F) * A = A * y) (hYp : ⁅Y, Y⁆ = Y)
    (hYc : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ Nat.card Y)
    {u : SpecialLinearGroup (Fin 4) F} (hu : u ∈ SK F (ne_zero_of_not_isSquare hns)) :
    ∃ y ∈ Y, (y : Matrix (Fin 4) (Fin 4) F) = P * u * P⁻¹ := by
  set hl := ne_zero_of_not_isSquare hns
  set φ := conjInv P hP with hφ
  have h2 := inv_mul_eq hP hAP
  have hle : Y.map φ ≤ CK F hl := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_CK_iff, hφ, coe_conjInv]
    calc P⁻¹ * (y : Matrix (Fin 4) (Fin 4) F) * P * kZero d = P⁻¹ * y * (A * P) := by
          rw [Matrix.mul_assoc _ P, hAP]
      _ = P⁻¹ * ((y : Matrix (Fin 4) (Fin 4) F) * A) * P := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (A * y) * P := by rw [hYA y hy]
      _ = P⁻¹ * A * y * P := by simp only [Matrix.mul_assoc]
      _ = kZero d * (P⁻¹ * y * P) := by rw [h2]; simp only [Matrix.mul_assoc]
  have hperf : ⁅Y.map φ, Y.map φ⁆ = Y.map φ := by rw [← Subgroup.map_commutator, hYp]
  have hleS : Y.map φ ≤ SK F hl :=
    le_trans (le_of_eq hperf.symm) (Subgroup.commutator_mono hle hle)
  have hcard : Nat.card (SK F hl) ≤ Nat.card (Y.map φ) := by
    rw [Subgroup.card_map_of_injective (conjInv_injective P hP)]
    exact (card_SK_le hl hns).trans hYc
  have heq : Y.map φ = SK F hl := Subgroup.eq_of_le_of_card_ge hleS hcard
  rw [← heq] at hu
  obtain ⟨y, hy, hyu⟩ := hu
  refine ⟨y, hy, ?_⟩
  have h3 := congrArg (fun z : SpecialLinearGroup (Fin 4) F => (z : Matrix (Fin 4) (Fin 4) F)) hyu
  simp only [hφ, coe_conjInv] at h3
  rw [← h3]
  simp only [Matrix.mul_assoc, mul_nonsing_inv P hP, Matrix.mul_one,
    mul_nonsing_inv_cancel_left P _ hP]

theorem trace_conj {P : Matrix (Fin 4) (Fin 4) F} (hP : IsUnit P.det)
    (u : Matrix (Fin 4) (Fin 4) F) : (P * u * P⁻¹).trace = u.trace := by
  rw [Matrix.trace_mul_cycle, nonsing_inv_mul P hP, Matrix.one_mul]

theorem eq_of_semilinear [Fintype F] (h2 : (2 : F) ≠ 0) {d : F} (hns : ¬ IsSquare d)
    {A : Matrix (Fin 4) (Fin 4) F} (hA : A * A = d • 1)
    {Y : Subgroup (SpecialLinearGroup (Fin 4) F)}
    (hYA : ∀ y ∈ Y, (y : Matrix (Fin 4) (Fin 4) F) * A = A * y) (hYp : ⁅Y, Y⁆ = Y)
    (hYc : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ Nat.card Y)
    {B : Matrix (Fin 4) (Fin 4) F} (hB : IsUnit B.det) (σ : F →+* F)
    (hBY : ∀ y ∈ Y, B * (y : Matrix (Fin 4) (Fin 4) F).map σ = y * B ∨
      B * (y : Matrix (Fin 4) (Fin 4) F).map σ = -(y * B)) :
    (∀ c, σ c = c) ∧ ∃ x z : F, B = x • 1 + z • A := by
  obtain ⟨P, hP, hAP⟩ := exists_mul_eq_mul_kZero hns hA
  set hl := ne_zero_of_not_isSquare hns
  have hl1 := ne_one_of_not_isSquare hns
  have h8 : (8 : F) ≠ 0 := by
    have : (8 : F) = 2 * 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero h2 h2) h2
  set Bσ := P⁻¹ * B * P.map σ with hBσ
  have key : ∀ u : SpecialLinearGroup (Fin 4) F, u ∈ SK F hl →
      (u : Matrix (Fin 4) (Fin 4) F).trace = 4 →
      Bσ * (u : Matrix (Fin 4) (Fin 4) F).map σ = u * Bσ := by
    intro u hu htr
    obtain ⟨y, hy, hyu⟩ := mem_of_card hns hP hAP hYA hYp hYc hu
    have htry : (y : Matrix (Fin 4) (Fin 4) F).trace = 4 := by rw [hyu, trace_conj hP, htr]
    have hyB : B * (y : Matrix (Fin 4) (Fin 4) F).map σ = y * B := by
      rcases hBY y hy with h | h
      · exact h
      · exfalso
        have h1 : B * (y : Matrix (Fin 4) (Fin 4) F).map σ * B⁻¹ =
            -(y : Matrix (Fin 4) (Fin 4) F) := by
          rw [h, Matrix.neg_mul, mul_nonsing_inv_cancel_right B _ hB]
        have h3 := congrArg Matrix.trace h1
        rw [Matrix.trace_mul_cycle, nonsing_inv_mul B hB, Matrix.one_mul, ← AddMonoidHom.map_trace,
          Matrix.trace_neg, htry, map_ofNat] at h3
        apply h8
        linear_combination h3
    have hPu : P * (u : Matrix (Fin 4) (Fin 4) F) = y * P := by
      rw [hyu, nonsing_inv_mul_cancel_right P _ hP]
    have hyP : P⁻¹ * (y : Matrix (Fin 4) (Fin 4) F) = u * P⁻¹ := by
      rw [hyu]
      simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left P _ hP]
    calc Bσ * (u : Matrix (Fin 4) (Fin 4) F).map σ
        = P⁻¹ * B * (P * (u : Matrix (Fin 4) (Fin 4) F)).map σ := by
          rw [hBσ, Matrix.map_mul, Matrix.mul_assoc]
      _ = P⁻¹ * B * ((y : Matrix (Fin 4) (Fin 4) F) * P).map σ := by rw [hPu]
      _ = P⁻¹ * (B * (y : Matrix (Fin 4) (Fin 4) F).map σ) * P.map σ := by
          rw [Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = P⁻¹ * ((y : Matrix (Fin 4) (Fin 4) F) * B) * P.map σ := by rw [hyB]
      _ = (P⁻¹ * (y : Matrix (Fin 4) (Fin 4) F)) * B * P.map σ := by simp only [Matrix.mul_assoc]
      _ = u * Bσ := by rw [hyP, hBσ]; simp only [Matrix.mul_assoc]
  have hdetσ : IsUnit (P.map σ).det := by
    rw [show (P.map σ).det = σ P.det by rw [RingHom.map_det, RingHom.mapMatrix_apply]]
    exact hP.map σ
  have hBσu : IsUnit Bσ.det := by
    rw [hBσ, det_mul, det_mul]
    exact ((isUnit_nonsing_inv_det P hP).mul hB).mul hdetσ
  obtain ⟨hσ, hBeq⟩ := eq_of_semilinear_comm_uK hl hBσu σ
    (key _ (slUK_mem_SK hl hl1 1 0) (trace_uK d 1 0))
    (key _ (slLK_mem_SK hl hl1 1 0) (trace_lK d 1 0))
    (key _ (slUK_mem_SK hl hl1 0 1) (trace_uK d 0 1))
    (fun c => key _ (slUK_mem_SK hl hl1 c 0) (trace_uK d c 0))
  refine ⟨hσ, Bσ 0 0, Bσ 1 0, ?_⟩
  have hPσ : P.map σ = P := by
    ext i j
    exact hσ _
  have hB' : B = P * Bσ * P⁻¹ := by
    rw [hBσ, hPσ]
    simp only [Matrix.mul_assoc, mul_nonsing_inv P hP, Matrix.mul_one,
      mul_nonsing_inv_cancel_left P _ hP]
  have hPK : P * kZero d * P⁻¹ = A := by
    rw [← hAP, mul_nonsing_inv_cancel_right P _ hP]
  have hB'' : B = P * (Bσ 0 0 • 1 + Bσ 1 0 • kZero d) * P⁻¹ := by
    conv_lhs => rw [hB', hBeq]
  rw [hB'', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    mul_nonsing_inv P hP, Matrix.mul_smul, Matrix.smul_mul, hPK]

end IdxSp

end CFSG.ComponentClassification.CatFactsL4U4
