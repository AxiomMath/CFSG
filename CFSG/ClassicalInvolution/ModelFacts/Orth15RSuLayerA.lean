module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuLevi

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
open scoped MatrixGroups

section Levs

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] noncomputable def levS (B : SL(2, K)) : Matrix (Fin 4) (Fin 4) K :=
  Lev (B : Matrix (Fin 2) (Fin 2) K) (conjTr σ ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))

variable {σ}

theorem levS_mul (B B' : SL(2, K)) : levS σ (B * B') = levS σ B * levS σ B' := by
  rw [levS, levS, levS, Lev_mul, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, conjTr_mul]

theorem levS_one : levS σ (1 : SL(2, K)) = 1 := by
  rw [levS, inv_one, Matrix.SpecialLinearGroup.coe_one, conjTr_one, Lev_one]

theorem conjTr_conjTr (hσσ : ∀ c, σ (σ c) = c) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    conjTr σ (conjTr σ M) = M := by
  ext i j
  simp [conjTr, hσσ]

theorem det_conjTr {n : ℕ} (M : Matrix (Fin n) (Fin n) K) : (conjTr σ M).det = σ M.det := by
  rw [conjTr, Matrix.det_transpose]
  exact (RingHom.map_det σ.toRingHom M).symm

theorem levS_unitary (hσσ : ∀ c, σ (σ c) = c) (B : SL(2, K)) :
    conjTr σ (levS σ B) * Gam * levS σ B = Gam := by
  have h1 : conjTr σ (B : Matrix (Fin 2) (Fin 2) K) *
      conjTr σ ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← conjTr_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, conjTr_one]
  have h2 : conjTr σ (conjTr σ ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) *
      (B : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [conjTr_conjTr hσσ, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  rw [levS, conjTr_Lev, Matrix.mul_assoc, Gam_Lev, ← Matrix.mul_assoc, Lev_mul, h1, h2, Lev_one,
    Matrix.one_mul]

theorem det_levS (B : SL(2, K)) : (levS σ B).det = 1 := by
  rw [levS, det_Lev, det_conjTr, (B⁻¹).2, B.2, map_one, mul_one]

theorem exists_conj_levS (hσσ : ∀ c, σ (σ c) = c) {A B : Matrix (Fin 2) (Fin 2) K}
    (h2 : conjTr σ B * A = 1) (B₁ : SL(2, K)) :
    ∃ B₂ : SL(2, K),
      Lev A B * levS σ B₁ * Lev (conjTr σ B) (conjTr σ A) = levS σ B₂ := by
  have hc1 : A * conjTr σ B = 1 := mul_eq_one_comm.mp h2
  have hdX : (A * (B₁ : Matrix (Fin 2) (Fin 2) K) * conjTr σ B).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, B₁.2, mul_one, ← Matrix.det_mul, hc1, Matrix.det_one]
  have hdY : (A * ((B₁⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * conjTr σ B).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, (B₁⁻¹).2, mul_one, ← Matrix.det_mul, hc1, Matrix.det_one]
  set X : SL(2, K) := ⟨A * (B₁ : Matrix (Fin 2) (Fin 2) K) * conjTr σ B, hdX⟩ with hX
  set Y : SL(2, K) :=
    ⟨A * ((B₁⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * conjTr σ B, hdY⟩ with hY
  have hXY : X * Y = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    show A * (B₁ : Matrix (Fin 2) (Fin 2) K) * conjTr σ B *
      (A * ((B₁⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * conjTr σ B) = 1
    calc A * (B₁ : Matrix (Fin 2) (Fin 2) K) * conjTr σ B *
        (A * ((B₁⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * conjTr σ B)
        = A * (B₁ : Matrix (Fin 2) (Fin 2) K) * (conjTr σ B * A) *
          ((B₁⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * conjTr σ B := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          have e : (B₁ : Matrix (Fin 2) (Fin 2) K) *
              ((B₁⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
            rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
              Matrix.SpecialLinearGroup.coe_one]
          rw [h2, Matrix.mul_one, Matrix.mul_assoc A, e, Matrix.mul_one, hc1]
  refine ⟨X, ?_⟩
  have hXi : X⁻¹ = Y := inv_eq_of_mul_eq_one_right hXY
  unfold levS
  rw [hXi, Lev_mul, Lev_mul]
  congr 1
  show B * conjTr σ ((B₁⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * conjTr σ A =
    conjTr σ (A * ((B₁⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * conjTr σ B)
  rw [conjTr_mul, conjTr_mul, conjTr_conjTr hσσ]
  simp only [Matrix.mul_assoc]

theorem exists_Gam_levS (hσσ : ∀ c, σ (σ c) = c) (B : SL(2, K)) :
    ∃ B' : SL(2, K), Gam * levS σ B * Gam = levS σ B' := by
  have hdet : (conjTr σ ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [det_conjTr, (B⁻¹).2, map_one]
  have hdet' : (conjTr σ (B : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [det_conjTr, B.2, map_one]
  set X : SL(2, K) := ⟨conjTr σ ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K), hdet⟩ with hX
  set Y : SL(2, K) := ⟨conjTr σ (B : Matrix (Fin 2) (Fin 2) K), hdet'⟩ with hY
  have hXY : X * Y = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    show conjTr σ ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      conjTr σ (B : Matrix (Fin 2) (Fin 2) K) = 1
    rw [← conjTr_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, conjTr_one]
  refine ⟨X, ?_⟩
  have hXi : X⁻¹ = Y := inv_eq_of_mul_eq_one_right hXY
  unfold levS
  rw [hXi, Gam_Lev, Matrix.mul_assoc, Gam_mul_Gam, Matrix.mul_one]
  show Lev (conjTr σ ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) (B : Matrix (Fin 2) (Fin 2) K)
    = Lev (conjTr σ ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))
      (conjTr σ (conjTr σ (B : Matrix (Fin 2) (Fin 2) K)))
  rw [conjTr_conjTr hσσ]

@[expose] def tSL {ω : K} (hω : ω * ω = -1) : SL(2, K) :=
  ⟨!![-ω, 0; 0, ω], by rw [Matrix.det_fin_two_of]; linear_combination (-1) * hω⟩

theorem coe_tSL {ω : K} (hω : ω * ω = -1) :
    ((tSL hω : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![-ω, 0; 0, ω] := rfl

theorem coe_tSL_inv {ω : K} (hω : ω * ω = -1) :
    (((tSL hω)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![ω, 0; 0, -ω] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_tSL, Matrix.adjugate_fin_two_of]
  simp

theorem levS_tSL {ω : K} (hω : ω * ω = -1) (hσω : σ ω = ω) :
    levS σ (tSL hω) = Matrix.diagonal ![-ω, ω, ω, -ω] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levS, Lev, conjTr, coe_tSL, hσω]

@[expose] def upSL : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_upSL : ((upSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := rfl

theorem coe_upSL_inv :
    (((upSL : SL(2, K))⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, -1; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_upSL, Matrix.adjugate_fin_two_of]
  simp

theorem levS_upSL : levS σ (upSL (K := K)) =
    (!![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, -1, 1] : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levS, Lev, conjTr, coe_upSL]

end Levs

section GroupA

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (SLayer isQuasisimple_of_equiv)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {ω : K}

local notation "σ₀" => unitaryInvolution K p f

structure AData (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p] (ω : K) :
    Prop where
  hK : Nat.card K = (p ^ f) ^ 2
  h2 : (2 : K) ≠ 0
  hω : ω * ω = -1
  hσω : unitaryInvolution K p f ω = ω

theorem AData.hσσ (h : AData K p f ω) :
    ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c :=
  unitaryInvolution_involutive h.hK

variable (h : AData K p f ω)

@[expose] noncomputable def iotaA : SL(2, K) →* Su K p f 4 where
  toFun B := mkSU K p f (Ya ω * levS σ₀ B * Yai ω)
    (by rw [det_conj (Ya_mul_Yai h.h2 h.hω), det_levS])
    (unitary_conj _ h.h2 (Ya_mul_Yai h.h2 h.hω) (conjTr_Ya_mul _ h.hω h.hσω)
      (levS_unitary h.hσσ B))
  map_one' := by
    apply suMat_injective
    rw [suMat_mkSU, levS_one, Matrix.mul_one, Ya_mul_Yai h.h2 h.hω, suMat_one]
  map_mul' B B' := by
    apply suMat_injective
    rw [suMat_mul, suMat_mkSU, suMat_mkSU, suMat_mkSU, levS_mul]
    calc Ya ω * (levS σ₀ B * levS σ₀ B') * Yai ω
        = Ya ω * levS σ₀ B * (Yai ω * Ya ω) *
          levS σ₀ B' * Yai ω := by
          rw [Yai_mul_Ya h.h2 h.hω, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem suMat_iotaA (B : SL(2, K)) :
    suMat (iotaA h B) = Ya ω * levS σ₀ B * Yai ω := rfl

theorem iotaA_injective : Function.Injective (iotaA h) := by
  intro B B' hB
  have h1 := congrArg suMat hB
  rw [suMat_iotaA, suMat_iotaA] at h1
  have h2 : levS σ₀ B = levS σ₀ B' := by
    have e : ∀ B : SL(2, K), levS σ₀ B =
        Yai ω * (Ya ω * levS σ₀ B * Yai ω) * Ya ω := fun B => by
      calc levS σ₀ B
          = (Yai ω * Ya ω) * levS σ₀ B * (Yai ω * Ya ω) := by
            rw [Yai_mul_Ya h.h2 h.hω, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e B, e B', h1]
  exact Subtype.ext (Lev_inj h2).1

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem Lev_mul_Delta (A B : Matrix (Fin 2) (Fin 2) K) (ω : K) :
    Lev A B * Matrix.diagonal ![ω, ω, -ω, -ω] = Matrix.diagonal ![ω, ω, -ω, -ω] * Lev A B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lev, Matrix.mul_diagonal, Matrix.diagonal_mul] <;> ring

theorem suMat_u0_Ya (h : AData K p f ω) :
    suMat (u0 K p f) * Ya ω = Ya ω * Matrix.diagonal ![ω, ω, -ω, -ω] := by
  rw [suMat_u0]
  exact U0_mul_Ya h.hω

theorem Yai_suMat_u0 (h : AData K p f ω) :
    Yai ω * suMat (u0 K p f) = Matrix.diagonal ![ω, ω, -ω, -ω] * Yai ω := by
  calc Yai ω * suMat (u0 K p f) = Yai ω * suMat (u0 K p f) * (Ya ω * Yai ω) := by
        rw [Ya_mul_Yai h.h2 h.hω, Matrix.mul_one]
    _ = Yai ω * (suMat (u0 K p f) * Ya ω) * Yai ω := by simp only [Matrix.mul_assoc]
    _ = Yai ω * (Ya ω * Matrix.diagonal ![ω, ω, -ω, -ω]) * Yai ω := by rw [suMat_u0_Ya h]
    _ = (Yai ω * Ya ω) * Matrix.diagonal ![ω, ω, -ω, -ω] * Yai ω := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal ![ω, ω, -ω, -ω] * Yai ω := by
        rw [Yai_mul_Ya h.h2 h.hω, Matrix.one_mul]

theorem iotaA_comm_u0 (B : SL(2, K)) : iotaA h B * u0 K p f = u0 K p f * iotaA h B := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_iotaA]
  calc Ya ω * levS σ₀ B * Yai ω * suMat (u0 K p f)
      = Ya ω * levS σ₀ B * (Yai ω * suMat (u0 K p f)) := by rw [Matrix.mul_assoc]
    _ = Ya ω * levS σ₀ B * (Matrix.diagonal ![ω, ω, -ω, -ω] * Yai ω) := by
        rw [Yai_suMat_u0 h]
    _ = Ya ω * (levS σ₀ B * Matrix.diagonal ![ω, ω, -ω, -ω]) * Yai ω := by
        simp only [Matrix.mul_assoc]
    _ = Ya ω * (Matrix.diagonal ![ω, ω, -ω, -ω] * levS σ₀ B) * Yai ω := by
        rw [levS, Lev_mul_Delta]
    _ = (Ya ω * Matrix.diagonal ![ω, ω, -ω, -ω]) * levS σ₀ B * Yai ω := by
        simp only [Matrix.mul_assoc]
    _ = suMat (u0 K p f) * Ya ω * levS σ₀ B * Yai ω := by rw [suMat_u0_Ya h]
    _ = suMat (u0 K p f) * (Ya ω * levS σ₀ B * Yai ω) := by simp only [Matrix.mul_assoc]

end GroupA

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
