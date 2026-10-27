module

public import CFSG.ClassicalInvolution.AschTight.S1911F0a
public import CFSG.ClassicalInvolution.Asc77.AscL62Aut

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem map_map_eq (σ : F ≃+* F) (hσ2 : ∀ x, σ (σ x) = x) (X : Matrix (Fin 2) (Fin 2) F) :
    (X.map σ).map σ = X := by
  ext i j
  simp [hσ2]

theorem exists_mul_map_eq_smul (σ : F ≃+* F) (hσ2 : ∀ x, σ (σ x) = x) (G : GL (Fin 2) F)
    (hinv : ∀ b, semilinHom G σ (semilinHom G σ b) = b) :
    ∃ l : F, l ≠ 0 ∧ σ l = l ∧
      (G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F).map σ = l • 1 := by
  set Gm : Matrix (Fin 2) (Fin 2) F := (G : Matrix (Fin 2) (Fin 2) F) with hGm
  set Gi : Matrix (Fin 2) (Fin 2) F := ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hGi
  have hGiG : Gi * Gm = 1 := by rw [hGm, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hone : (1 : Matrix (Fin 2) (Fin 2) F).map σ = 1 := Matrix.map_one σ (map_zero σ) (map_one σ)
  set M := Gm * Gm.map σ with hM
  have hN : (Gi.map σ * Gi) * M = 1 := by
    calc (Gi.map σ * Gi) * M = Gi.map σ * ((Gi * Gm) * Gm.map σ) := by
          simp only [hM, Matrix.mul_assoc]
      _ = Gi.map σ * Gm.map σ := by rw [hGiG, Matrix.one_mul]
      _ = (Gi * Gm).map σ := Matrix.map_mul.symm
      _ = 1 := by rw [hGiG, hone]
  have hcomm : ∀ b : SL(2, F), M * (b : Matrix (Fin 2) (Fin 2) F) =
      (b : Matrix (Fin 2) (Fin 2) F) * M := by
    intro b
    have h := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) (hinv b)
    simp only [coe_semilinHom] at h
    rw [← hGm, ← hGi, Matrix.map_mul, Matrix.map_mul, map_map_eq σ hσ2] at h
    calc M * (b : Matrix (Fin 2) (Fin 2) F)
        = M * (b : Matrix (Fin 2) (Fin 2) F) * ((Gi.map σ * Gi) * M) := by
          rw [hN, Matrix.mul_one]
      _ = (Gm * (Gm.map σ * (b : Matrix (Fin 2) (Fin 2) F) * Gi.map σ) * Gi) * M := by
          simp only [hM, Matrix.mul_assoc]
      _ = (b : Matrix (Fin 2) (Fin 2) F) * M := by rw [h]
  obtain ⟨l, hMs⟩ : ∃ l : F, M = l • (1 : Matrix (Fin 2) (Fin 2) F) :=
    ⟨_, eq_smul_one_of_commute M hcomm⟩
  refine ⟨l, ?_, ?_, hMs⟩
  · intro h0
    rw [h0, zero_smul] at hMs
    rw [hMs, Matrix.mul_zero] at hN
    exact zero_ne_one hN
  · have h1 : Gm.map σ * Gm = l • (1 : Matrix (Fin 2) (Fin 2) F) := by
      calc Gm.map σ * Gm = Gi * M * Gm := by
            rw [hM, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
        _ = l • (1 : Matrix (Fin 2) (Fin 2) F) := by
            rw [hMs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hGiG]
    have h2 : (Gm.map σ * Gm).map σ = M := by rw [Matrix.map_mul, map_map_eq σ hσ2, hM]
    rw [h1, hMs] at h2
    have h3 := congrFun (congrFun h2 0) 0
    simpa using h3

theorem exists_mul_map_eq_self [Finite F] {m : ℕ} (hF : Nat.card F = m ^ 2) (hm : 3 ≤ m)
    (σ : F ≃+* F) (hσ : ∀ x, σ x = x ^ m) (hσ2 : ∀ x, σ (σ x) = x)
    (A : Matrix (Fin 2) (Fin 2) F) (hA : A * A.map σ = 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, IsUnit P.det ∧ A * P.map σ = P := by
  obtain ⟨α, hα⟩ := exists_det_smul_add_ne_zero hF hm A
  refine ⟨α • 1 + α ^ m • A, isUnit_iff_ne_zero.mpr hα, ?_⟩
  rw [← hσ α]
  have h1 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + σ α • A).map σ =
      σ α • (1 : Matrix (Fin 2) (Fin 2) F) + α • A.map σ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hσ2]
  rw [h1, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, hA, add_comm]

theorem semilinHom_eq_self_iff (σ : F ≃+* F) (G : GL (Fin 2) F) {c : F}
    (hc : c ≠ 0) {P : Matrix (Fin 2) (Fin 2) F} (hP : IsUnit P.det)
    (hGP : (c⁻¹ • (G : Matrix (Fin 2) (Fin 2) F)) * P.map σ = P) (b : SL(2, F)) :
    semilinHom G σ b = b ↔ (P⁻¹ * (b : Matrix (Fin 2) (Fin 2) F) * P).map σ =
      P⁻¹ * (b : Matrix (Fin 2) (Fin 2) F) * P := by
  set Gm : Matrix (Fin 2) (Fin 2) F := (G : Matrix (Fin 2) (Fin 2) F) with hGm
  set Gi : Matrix (Fin 2) (Fin 2) F := ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hGi
  set B : Matrix (Fin 2) (Fin 2) F := (b : Matrix (Fin 2) (Fin 2) F) with hB
  have hGGi : Gm * Gi = 1 := by rw [hGm, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hone : (1 : Matrix (Fin 2) (Fin 2) F).map σ = 1 := Matrix.map_one σ (map_zero σ) (map_one σ)
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hPs : P.map σ * P⁻¹.map σ = 1 := by rw [← Matrix.map_mul, hPPi, hone]
  set A : Matrix (Fin 2) (Fin 2) F := c⁻¹ • Gm with hA
  have hAP : A = P * P⁻¹.map σ := by
    calc A = A * (P.map σ * P⁻¹.map σ) := by rw [hPs, Matrix.mul_one]
      _ = P * P⁻¹.map σ := by rw [← Matrix.mul_assoc, hGP]
  have e1 : semilinHom G σ b = b ↔ Gm * B.map σ = B * Gm := by
    constructor
    · intro h
      have h' := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) h
      simp only [coe_semilinHom] at h'
      exact mul_eq_of_conj_eq G h'
    · intro h
      apply Subtype.ext
      rw [coe_semilinHom, ← hGm, ← hGi, ← hB, h, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  have e2 : Gm * B.map σ = B * Gm ↔ A * B.map σ = B * A := by
    rw [hA, Matrix.smul_mul, Matrix.mul_smul]
    constructor
    · intro h
      rw [h]
    · intro h
      have := congrArg (fun X => c • X) h
      simpa [smul_smul, mul_inv_cancel₀ hc] using this
  rw [e1, e2, Matrix.map_mul, Matrix.map_mul]
  constructor
  · intro h
    have key : P * (P⁻¹.map σ * B.map σ * P.map σ) = B * P := by
      calc P * (P⁻¹.map σ * B.map σ * P.map σ) = (P * P⁻¹.map σ) * B.map σ * P.map σ := by
            simp only [Matrix.mul_assoc]
        _ = B * A * P.map σ := by rw [← hAP, h]
        _ = B * P := by rw [Matrix.mul_assoc, hGP]
    calc P⁻¹.map σ * B.map σ * P.map σ = P⁻¹ * (P * (P⁻¹.map σ * B.map σ * P.map σ)) := by
          rw [← Matrix.mul_assoc P⁻¹ P, hPiP, Matrix.one_mul]
      _ = P⁻¹ * B * P := by rw [key, Matrix.mul_assoc]
  · intro h
    calc A * B.map σ = P * P⁻¹.map σ * B.map σ * (P.map σ * P⁻¹.map σ) := by
          rw [hPs, Matrix.mul_one, hAP]
      _ = P * (P⁻¹.map σ * B.map σ * P.map σ) * P⁻¹.map σ := by simp only [Matrix.mul_assoc]
      _ = (P * P⁻¹) * B * (P * P⁻¹.map σ) := by rw [h]; simp only [Matrix.mul_assoc]
      _ = B * A := by rw [hPPi, Matrix.one_mul, ← hAP]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
